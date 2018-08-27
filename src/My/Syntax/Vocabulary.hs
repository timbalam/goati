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


-- | A nested group of paths. Type is equivalent to 'F (M.Map Ident)',
-- the Church-encodedfFree monad for 'M.Map Ident'.
newtype Group a = Group { runGroup :: forall x . (a -> x) -> (M.Map Ident x -> x) -> x }

wrapGroup :: M.Map Ident (Group a) -> Group a
wrapGroup m = Group (\ kp kf -> kf (M.map (\ (Group eval) -> eval kp kf) m))

-- | A top-level block of assignments partitioned by visibility.
newtype Block a = Block (forall x . (a -> x) -> (M.Map Ident x -> x) -> (M.Map Ident x, M.Map Ident x))

instance S.Block (Collect [DefnError] (Block a)) where
  type Rec (Collect [DefnError] (Block a)) = ChkRec
    (Collect [DefnError] (Group a))
    (ChkStmtS (Collect [DefnError] (Group a)))
  block_ s = checkRec (coerce (Just . checkStmtS wrapGroup <$> s)) <$> (\ (Identity (l,s)) ->
    Block (\ kp kf -> 
      (M.map (\ (Group eval) -> eval kp kf) l, M.map (\ (Group eval) -> eval kf kp) s)))
  
    
-- | A top-level tuple block.
newtype Tuple a = Tuple (forall x. (a -> x) -> (M.Map Ident x -> x) -> M.Map Ident x)

instance S.Tuple (Collect [DefnError] (Tuple a)) where
  type Tup (Collect [DefnError] (Tuple a) = ChkTup
    (Collect [DefnError] (Group a))
    (ChkStmtS (Collect [DefnError] (Group a)))
  tup_ (ChkTup s) = checkStmts (coerce (checkStmtS wrapGroup <$> s)) <&> (\ (Identity m) ->
    Tuple (\ kp kf -> M.Map (\ (Group eval) -> eval kp kf) m))
  
  
-- | The lhs of an assignment is a single name or a name and nested lhs. Second field 
-- is equivalent to Church-encoded 'Maybe p'.
data Path p = Path Ident (forall x . x -> (p -> x) -> x)

-- | Associate assigned names to nested statements.
newtype ChkStmts a s = ChkStmts (M.Map Ident ([a], Either a s))
  deriving Functor
  
-- | Church-encoded fix-point with some associated type classes
newtype ChkStmtS a = ChkStmtS (forall x. (S.Let x, S.Rhs x ~ a, S.Splus x)
  => (ChkStmts a x -> x) -> x)
  deriving Functor

instance S.Self (Path p) where self_ i = Path i (\ nothing _ -> nothing)
instance S.Local (Path p) where local_ i = Path i (\ nothing _ -> nothing)
  
instance S.RelPath p => S.Field (Path p) where
  type Compound (Path p) = Path (Compound p)
  Path i maybe #. k = Path i (\ _ just -> just (maybe (S.self_ k) (#. k)))
  
instance (S.Let s, S.Rhs s ~ a) => S.Let (ChkStmts a s) where
  type Lhs (ChkStmts a s) = Path (S.Lhs s)
  type Rhs (ChkStmts a s) = a
  Path i maybe #= a = (ChkStmts . M.singleton i . (,) []) (maybe (Left a) (Right . (#= a)))
  
instance (S.Let s, S.Rhs s ~ a) => S.Let (ChkStmtS a s) where
  type Lhs (ChkStmtS a s) = Path (S.Lhs s)
  type Rhs (ChkStmtS a s) = a
  p #= a = ChkStmts (\ k -> k (p #= a))
  
instance S.Sep s => S.Sep (ChkStmts a s) where
  ChkStmts m1 #: ChkStmts m2 = ChkStmts (M.unionWith f m1 m2) where
    f (xs1, Left x  ) (xs2, e       ) = ([x1]++xs1++xs2, e         )
    f (xs1, e       ) (xs2, Left x  ) = (xs1++[x]++xs2 , e         )
    f (xs1, Right s1) (xs2, Right s2) = (xs1++xs2      , s1 S.#: s2)
    
instance S.Sep s => S.Sep (ChkStmtS a s) where
  ChkStmtS f #: ChkStmtS g = ChkStmtS h where
    h :: S.Sep s => (ChkStmts s a -> a) -> a
    h k = f (\ s1 -> g (\ s2 -> k (s1 #: s2)))
    
instance S.Splus (ChkStmts a s) where empty_ = ChkStmts M.empty
instance S.Splus (ChkStmtS a s) where empty_ = ChkTup (\ k -> k S.empty_)


-- | A set of statements from a tuple block, including desugaring punned assignments.
newtype ChkTup a s = ChkTup (ChkStmts a s)

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun a = Pun (forall p. S.RelPath p => p) a

pun :: (S.Let s, S.RelPath (S.Lhs s), S.Rhs s ~ a) => Pun a -> ChkTup a s
pun (Pun p a) = ChkTup (p #= a)

instance S.Self a => S.Self (Pun a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance S.Local a => S.Local (Pun a) where local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field a => S.Field (Pun a) where
  type Compound (Pun a) = Pun (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

instance (S.Let s, S.RelPath (S.Lhs s), S.Rhs s ~ a, S.Self a)
  => S.Self (ChkTup a s) where self_ i = pun (S.self_ i)
instance (S.Let s, S.RelPath (S.Lhs s), S.Rhs s ~ a, S.Local a)
  => S.Local (ChkTup a s) where local_ i = pun (S.local_ i)

instance (S.Let s, S.RelPath (S.Lhs s), S.Rhs s ~ a, S.Field a) => S.Field (ChkTup a s) where
  type Compound (ChkTup a s) = Pun (S.Compound a)
  p #. k = pun (p S.#. k)

instance (S.Let s, S.RelPath (S.Lhs s), S.Rhs s ~ a) => S.Let (ChkTup a s) where
  type Lhs (ChkTup a) = forall p. S.RelPath p => Path p
  type Rhs (ChkTup a) = a
  p #= a = ChkTup (p #= a)

instance S.Sep s => S.Sep (ChkTup a s) where ChkTup f #: ChkTup g = ChkTup (f #: g)
instance S.Splus (ChkTup a s) where empty_ = ChkTup S.empty_


-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value,
-- indicating that the path is to be checked for ambiguity but not assigned a value.
data ChkRec a s = ChkRec { local = ChkStmts (Maybe a) s, public = ChkStmts (Maybe a) s }

-- | A decomposable value.
-- Equivalent to the Church-encoded free monad for 'M.Map Ident :.: Maybe'.
newtype Ungroup a = Ungroup { runUngroup :: forall x . (a -> x) -> (M.Map Ident (Maybe x) -> x) -> x }

instance S.Field a => S.Field (Ungroup a) where
  type Compound (Ungroup a) = Ungroup (S.Compound a)
  Ungroup eval #. i = Ungroup (\ kp kf -> eval (\ a -> kp (a S.#. i)) kf)

  
decl :: Path s -> ChkRec a s
decl (Path i maybe) = ChkRec
  { local = S.empty_
  , public = ChkStmts (M.singleton i ([], maybe (Left Nothing) Right))
  }
  
instance S.Self (ChkRec a s) where self_ i = decl (S.self_ i)
  
instance S.RelPath s => S.Field (ChkRec a s) where
  type Compound (ChkRec a s) = Path s
  p #. k = decl (p S.#. k)

instance S.Path a => S.Let (ChkRec a s) where
  type Lhs (ChkRec a s) = ChkPatt s
  type Rhs (ChkRec a s) = Ungroup a
  ChkPatt k #= Ungroup eval = k (eval id)

instance S.Sep s => S.Sep (ChkRec a s) where
  ChkRec{local=l1,public=s1} #: ChkRec{local=l2,public=s2} =
    ChkRec { local = l1 S.#: l2, public = s1 S.#: s2 }

instance S.Splus (ChkRec a s) where
  empty_ = ChkRec{local=S.empty_,public=S.empty_}


-- | A pattern definition represents the simultaneous decomposing a value into distinct
-- parts and the assignment of the parts
newtype ChkPatt s = ChkPatt (forall x. Path x
  => (M.Map Ident (Maybe x) -> x) -> x -> ChkRec x s)
newtype ChkDecomp s = ChkDecomp (forall x. Path x
  => (M.Map Ident (Maybe x) -> x) -> x -> (Endo (ChkRec x s), x)

letpath
  :: (forall x. S.RelPath x => P.Vis (Path x) (Path x)) -> ChkPatt s
letpath (P.Pub p) = ChkPatt (\ _ a -> ChkRec S.empty_ (p #= a))
letpath (P.Priv p) = ChkPatt (\ _ a -> ChkRec (p #= a) S.empty_)

decomp :: ChkDecomp s -> ChkPatt s
decomp (ChkDecomp eval) = ChkPatt (\ kf a -> appEndo (fst (eval kf a)) S.empty_)

 
instance S.Self (ChkPatt a) where self_ i = letpath (S.self_ i)
instance S.Local (ChkPatt a) where local_ i = letpath (S.local_ i)
  
instance S.Field (ChkPatt a) where
  type Compound (ChkPatt a) = forall x. RelPath x => P.Vis (Path x) (Path x)
  v #. k = letpath (v S.#. k)

type instance S.Member (ChkPatt s) = ChkPatt s

instance S.Tuple (Collect [DefnError] (ChkPatt s)) where
  type Tup (Collect [DefnError] (ChkPatt s)) =
    ChkTup (Collect [DefnError] (Group (ChkPatt s)))
      (ChkStmtS (Collect [DefnError] (Group (ChkPatt s))))
  tup_ s = decomp <$> tup_ s
      
      
instance S.Tuple (Collect [DefnError] (ChkDecomp s)) where
  type Tup (Collect [DefnError] (ChkDecomp s)) =
    ChkTup (Collect [DefnError] (Group (ChkPatt s)))
      (ChkStmtS (Collect [DefnError] (Group (ChkPatt s))))
  tup_ (ChkTup s) = checkStmts (checkStmtS wrap <$> s) <&> (\ m ->
    ChkDecomp (\ kf a -> kf <$> M.traverseWithKey
      (\ i (Group eval) ->
        eval
          (\ (ChkPatt eval) -> ((eval kf (a S.#. i) S.#:), Nothing))
          (fmap (Just . kf) . sequenceA)
      m)))
     
  
instance S.Extend (Collect [DefnError] (ChkPatt s)) where
  type Ext (Collect [DefnError] (ChkPatt s)) = Collect [DefnError] (ChkDecomp s)
  p1 # p2 = liftA2 ext where
    ext (ChkPatt f) (ChkDecomp g) = ChkPatt (\ kf a -> let (Endo k, a') = g kf a in k (f kf a'))
  

  

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
          
checkStmtS
  :: Functor f
  => (M.Map Ident a -> a)
  -> ChkStmtS (Collect [DefnError] (f a))
  -> Collect [DefnError] (f a)
checkStmtS kf (ChkStmts eval) = eval (getCompose . fmap kf . Compose . checkStmts)


checkRec
  :: Applicative f
  => ChkRec (Collect [DefnError] (f a)) (Maybe (Collect [DefnError] (f a)))
  -> Collect [DefnError a] (f (M.Map Ident (Maybe a), M.Map Ident (Maybe a)))
checkRec (ChkRec{local=l,public=s}) =
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

