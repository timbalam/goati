{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | The '[DefnError]' type implements an abstract interpretation for validating sets of 
-- definitions made using the syntax classes for duplicated names, overlapping definitions, 
-- etc. 
module My.Syntax.Vocabulary
  ( DefnError(..) )
  where

import qualified My.Types.Parser as P
import My.Types.Repr (Ident)
import My.Types.Classes (MyError(..))
import qualified My.Types.Syntax.Class as S
import My.Util (Collect(..), collect)
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free.Church (MonadFree(..), F)
import Data.Semigroup
import Data.String (IsString(..))
import Data.Functor.Plus (Plus(..), Alt(..))
import Data.Typeable
import qualified Data.Map as M
--import qualified Data.Set as S


-- | Errors from binding definitions
data DefnError =
    OlappedMatch (P.Path P.Key)
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet P.VarPath
  -- ^ Error if a group assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately in a group
  deriving (Eq, Show, Typeable)
  
instance MyError DefnError where
  displayError (OlappedMatch p) = "Ambiguous destructuring of path " ++ show p
  displayError (OlappedSet p) = "Ambiguous assignment to path " ++ show p
  displayError (OlappedVis i) = "Variable assigned with multiple visibilities " ++ show i
  
  
-- | Applicative checking of definitions
newtype Check = Check [DefnError]
  deriving (Semigroup, Monoid)

instance S.Self Check where self_ _ = mempty
instance S.Local Check where local_ _ = mempty
  
instance S.Field Check where
  type Compound Check = Check
  es #. _ = es

instance Num Check where
  fromInteger = mempty
  (+) = (<>)
  (-) = (<>)
  (*) = (<>)
  negate = id
  abs = id
  signum = id

instance Fractional Check where
  fromRational = mempty
  (/) = (<>)

instance IsString Check where
  fromString = mempty

instance S.Lit Check where
  unop_ _ = id
  binop_ _ = (<>)

type instance S.Member Check = Check


newtype ChkTuple = ChkTuple (forall x. (M.Map Ident x -> x) -> x)
-- ^ church-encoded 'Fix (M.Map Ident)'

instance S.Tuple (Collect [DefnError] ChkTuple) where
  type Tup (Collect [DefnError] ChkTuple) = ChkTup (Collect [DefnError] ChkTuple)
  tup_ (ChkTup f) = f (\ s -> checkStmts s <&> (\ m -> ChkTuple ($ m)))
  
  
newtype ChkBlock = ChkBlock (forall x. (M.Map Ident x -> M.Map Ident x -> x) -> x)

instance S.Block (Collect [DefnError] ChkBlock) where
  type Rec (Collect [DefnError] ChkBlock) = ChkRec (Collect [DefnError] ChkBlock)
  block_ (ChkRec f) = f (\ l s -> checkRec l s <$> (\ (l, s) -> ChkBlock (\ k -> k l s)))
  
  
  
-- | The lhs of an assignment is a single name or a name and nested lhs.
data ChkPath p = ChkPath
  Ident
  (forall x . x -> (p -> x) -> x)
  -- ^ church-encoded 'Maybe p'

newtype ChkStmts a s = ChkStmts (M.Map Ident ([a], Either a s))
  deriving Functor

instance S.Self (ChkPath p) where self_ i = ChkPath i (\ nothing _ -> nothing)
instance S.Local (ChkPath p) where local_ i = ChkPath i (\ nothing _ -> nothing)
  
instance S.RelPath p => S.Field (ChkPath p) where
  type Compound (ChkPath p) = ChkPath (Compound p)
  ChkPath i maybe #. k = ChkPath i (\ _ just -> just (maybe (S.self_ k) (#. k)))
  
instance (S.Let s, S.Rhs s ~ a) => S.Let (ChkStmts a s) where
  type Lhs (ChkStmts a s) = ChkPath (S.Lhs s)
  type Rhs (ChkStmts a s) = a
  ChkPath i maybe #= a = (ChkStmts . M.singleton i . (,) []) (maybe (Left a) (Right . (#= a)))
  
instance S.Sep s => S.Sep (ChkStmts a s) where
  ChkStmts m1 #: ChkStmts m2 = ChkStmts (M.unionWith f m1 m2) where
    f (xs1, Left x  ) (xs2, e       ) = ([x1]++xs1++xs2, e         )
    f (xs1, e       ) (xs2, Left x  ) = (xs1++[x]++xs2 , e         )
    f (xs1, Right s1) (xs2, Right s2) = (xs1++xs2      , s1 S.#: s2)
    
instance S.Splus (ChkStmts a s) where empty_ = ChkStmts M.empty

-- | A 'Tuple' definition associates a group of paths with values.
newtype ChkTup a = ChkTup (forall x. (S.TupStmt x, S.Rhs x ~ a) => (ChkStmts a x -> x) -> x)

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun a = Pun (forall p. S.RelPath p => p) a

pun :: Pun a -> ChkTup a
pun (Pun p a) = ChkTup (\ k -> k (p #= a))

instance S.Self a => S.Self (Pun a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance S.Local a => S.Local (Pun a b) where local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field a => S.Field (Pun a) where
  type Compound (Pun a) = Pun (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

instance S.Self a => S.Self (ChkTup a) where self_ i = pun (S.self_ i)
instance S.Local a => S.Local (ChkTup a) where local_ i = pun (S.local_ i)

instance  S.Field a => S.Field (ChkTup a) where
  type Compound (ChkTup a) = Pun (S.Compound a)
  p #. k = pun (p S.#. k)

instance S.Let (ChkTup a) where
  type Lhs (ChkTup a) = forall p. S.RelPath p => ChkPath p
  type Rhs (ChkTup a) = a
  p #= a = ChkTup (\ k -> k (p #= a))

instance S.Sep s => S.Sep (ChkTup a s) where
  ChkTup f #: ChkTup g = ChkTup h where
    h :: S.Sep s => (ChkStmts s a -> a) -> a
    h k = f (\ s1 -> g (\ s2 -> k (s1 #: s2)))
  
instance S.Splus (ChkTup a s) where empty_ = ChkTup (\ k -> k S.empty_)


-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value, indicating that the path is to be 
-- checked for ambiguity but not assigned a value.
newtype ChkRec a = ChkRec
  (forall x. (RecStmt x, S.Rhs x ~ a)
    => ChkStmts (Maybe a) x
       -- ^ local paths
    -> ChkStmts (Maybe a) x
       -- ^ public paths
    -> x)
  
decl :: ChkPath s -> ChkRec a s
decl (ChkPath i maybe) = ChkRec
  { local = S.empty_
  , public = ChkStmts (M.singleton i ([], maybe (Left Nothing) Right))
  }
  
instance S.Self (ChkRec a s) where
  self_ i = decl (S.self_ i)
  
instance S.RelPath s => S.Field (ChkRec a s) where
  type Compound (ChkRec a s) = ChkPath s
  p #. k = decl (p S.#. k)

instance S.Let (ChkRec a s) where
  type Lhs (ChkRec a s) = ChkPatt s
  type Rhs (ChkRec a s) = a
  ChkPatt b #= a = b a

instance S.Sep s => S.Sep (ChkRec a s) where
  ChkRec{local=l1,public=s1} #: ChkRec{local=l2,public=s2} =
    ChkRec { local = l1 S.#: l2, public = s1 S.#: s2 }

instance S.Splus (ChkRec a s) where
  empty_ = ChkRec{local=S.empty_,public=S.empty_}


-- | A pattern definition represents the simultaneous decomposing a value into distinct
-- parts and the assignment of the parts
newtype ChkPatt a = ChkPatt ((a -> ChkRec a) -> a -> ChkRec a)

letpath
  :: (forall x. S.RelPath x => P.Vis (ChkPath x) (ChkPath x)) -> ChkPatt a
letpath (P.Pub p) = ChkPatt (\ _ a -> ChkRec (\ k -> k S.empty_ (p #= a)))
letpath (P.Priv p) = ChkPatt (\ _ a -> ChkRec (\ k -> k (p #= a) S.empty_))

 
instance S.Self (ChkPatt a) where self_ i = letpath (S.self_ i)
instance S.Local (ChkPatt a) where local_ i = letpath (S.local_ i)
  
instance S.Field (ChkPatt a) where
  type Compound (ChkPatt a) = forall x. RelPath x => P.Vis (ChkPath x) (ChkPath x)
  v #. k = letpath (v S.#. k)

type instance S.Member (ChkPatt a) = ChkPatt a

instance S.Path a => S.Tuple (Collect [DefnError] (ChkPatt a)) where
  type Tup (Collect [DefnError] (ChkPatt a)) = ChkTup (Collect [DefnError] (ChkPatt a))
  tup_ (ChkTup f) = f (\ s -> checkStmts s <&> (\ m ->
    ChkPatt (\ k a -> M.foldrWithKey (\ i (ChkPatt f) ->   
  
instance S.Extend (ChkPatt a) where
  type Ext (ChkPatt a) = ChkPatt a
  ChkPatt k1 # ChkPatt k2 = ChkPatt (\ k -> k2 (k1 k))
  

checkDecomp
  :: (S.Let s, S.Tuple (S.Lhs s))
  => ChkDecomp (S.Lhs s) (S.Tup (S.Lhs s)) -> S.Rhs s -> ChkDecomp s s
checkDecomp (ChkDecomp (ChkTup (ChkStmts m))) a =
  (ChkDecomp . ChkTup . ChkStmts) (M.mapWithKey f m)
  where 
    f i (xs, e) = (fmap (S.#= a') xs, bimap (S.#= a') ((S.#= a') . tup_) e) where
      a' = a #. i
  

-- | Validate that a set of names are unambiguous, or introduces 'OlappedSet' errors for
-- ambiguous names.
checkStmts
  :: Applicative f
  => ChkStmts (Collect [DefnError] (f a)) (Collect [DefnError] (f a))
  -> Collect [DefnError] (f (M.Map Ident a))
checkStmts (ChkStmts m) = getCompose (M.traverseWithKey f m) where
  f i ([], e) = Compose (either id id e)
  f i (_, e) = (Compose . collect . pure . OlappedSet . P.Pub . P.Pure) (P.K_ i) *>
    Compose (either id id e)


checkRec
  :: Applicative f
  => ChkStmts (Collect [DefnError] (f a))
  -> ChkStmts (Collect [DefnError] (f a))
  -> Collect [DefnError a] (f (M.Map Ident (Maybe a), M.Map Ident (Maybe a)))
checkRec l s =
  getCompose (checkVis (M.intersectionWith (,) l s) *> liftA2 (,) (checkLoc l) (checkPub s))
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    checkVis = M.traverseWithKey (const . Compose . collect . pure . OlappedVis)
    checkLoc = M.traverseMaybeWithKey f
    checkPub = M.traverseMaybeWithKey f
    
    f i ([], mb) = traverse (Compose (either id id) mb)
    f i (_, mb) = (Compose . collect . pure . OlappedSet . P.Pub . P.Pure) (P.K_ i) *>
      traverse (Compose (either id ide e))
      
-- | Tree of paths with one or values contained in leaves and zero or more
-- in internal nodes
--
-- Semigroup and monoid instances defined will union subtrees recursively
-- and accumulate values.
data Amb a = a `Overlap` Maybe (Amb a) | Disjoint (M.Map Ident (Amb a))
  deriving (Functor, Foldable, Traversable)
  
instance Applicative Amb where
  pure a = a `Overlap` Nothing
  (<*>) = ap
  
instance Monad Amb where
  return = pure
  
  a `Overlap` Nothing >>= k = k a
  a `Overlap` Just as >>= k = k a <!> (as >>= k)
  Disjoint fa >>= k = Disjoint (M.map (>>= k) fa)
  
instance MonadFree (M.Map Ident) Amb where
  wrap = Disjoint
  
instance Alt Amb where
  x `Overlap` Just a <!> b = (Overlap x . Just) (a <!> b)
  x `Overlap` Nothing <!> b = x `Overlap` Just b
  a <!> x `Overlap` Nothing = x `Overlap` Just a
  a <!> x `Overlap` Just b = (Overlap x . Just) (a <!> b)
  Disjoint fa <!> Disjoint fb = Disjoint (M.unionWith (<!>) fa fb)

