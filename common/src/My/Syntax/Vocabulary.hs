{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | The '[DefnError]' type implements an abstract interpretation for validating sets of 
-- definitions made using the syntax classes for duplicated names, overlapping definitions, 
-- etc. 
module My.Syntax.Vocabulary
  ( DefnError(..), Rec(..)
  , ChkTup(..), checkTup, checkDecomp
  , ChkRec(..), checkRec, buildRec
  , Node(..), checkNode
  , Path(..), ChkStmts(..)
  )
  where

import qualified My.Types.Parser as P
import My.Types.Repr (Ident)
import My.Types.Classes (MyError(..))
import qualified My.Types.Syntax.Class as S
import My.Util (Collect(..), collect, (<&>), traverseMaybeWithKey)
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free.Church (MonadFree(..), F(..))
import Control.Monad.State (state, evalState)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce (coerce)
--import Data.Functor.Classes (Show1(..), showsPrec1)
import Prelude.Extras (Show1(..), Lift1(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Foldable (Fix(..))
import Data.Maybe (mapMaybe)
import Data.Semigroup
import Data.String (IsString(..))
import Data.Functor.Plus (Plus(..), Alt(..))
import Data.Typeable
import qualified Data.Map as M
import Data.Void


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
  
 
-- | A set of overlapping statements
infixr 5 :?
data ChkStmts a s = Either a s :? [a]

instance Functor (ChkStmts a) where
  fmap f (e :? xs) = fmap f e :? xs

instance Semigroup s => Semigroup (ChkStmts a s) where
  (e       :? xs) <> (Left y  :? ys) = e              :? (xs ++ (y:ys))
  (Left x  :? xs) <> (e       :? ys) = e              :? x : (xs ++ ys)
  (Right a :? xs) <> (Right b :? ys) = Right (a <> b) :? (xs ++ ys)
  
instance Bifunctor ChkStmts where
  bimap f g (e :? xs) = bimap f g e :? fmap f xs
  
instance Bifoldable ChkStmts where
  bifoldMap f g (e :? xs) = bifoldMap f g e `mappend` foldMap f xs
  
instance Bitraversable ChkStmts where
  bitraverse f g (e :? xs) = liftA2 (:?) (bitraverse f g e) (traverse f xs)
  
instance Show a => Show1 (ChkStmts a) where
  showsPrec1 i (e :? xs) = showParen (i > 5)
    (showsPrec 6 e . showString " :? " . showsPrec 6 xs)
    
instance (Show a, Show s) => Show (ChkStmts a s) where
  showsPrec = showsPrec1
    
  
-- | Set of internal node statements sorted by name, represented as an unfold over nested
-- statements.
newtype Node a = Node { runNode :: forall x. (M.Map Ident (ChkStmts a x) -> x) -> x  }
newtype ChkMap a s = ChkMap { getChkMap :: M.Map Ident (ChkStmts a s) }
  deriving (Functor, Show)
  
toFix :: Node a -> Fix (ChkMap a)
toFix (Node k) = k (Fix . ChkMap)

fromFix :: Fix (ChkMap a) -> Node a
fromFix (Fix m) = (fixNode . getChkMap) (fmap fromFix m)

instance Show a => Show (Node a) where
  showsPrec d n = showParen (d > 10)
    (showString "fromFix" . showsPrec 11 (toFix n))

fixNode :: M.Map Ident (ChkStmts a (Node a)) -> Node a
fixNode m = Node (\ k -> k (fmap (fmap (`runNode` k)) m))

unfixNode :: Node a -> M.Map Ident (ChkStmts a (Node a))
unfixNode (Node f) = f ((fmap . fmap) fixNode)

checkNode :: (Ident -> DefnError) -> Node (Collect [DefnError] a) -> Collect [DefnError] (F (M.Map Ident) a)
checkNode f (Node k) = (checkNode' f . k) (fmap run) where
  run
    :: ChkStmts
      (Collect [DefnError] a)
      (M.Map Ident (ChkStmts (Collect [DefnError] (F (M.Map Ident) a)) Void))
    -> ChkStmts (Collect [DefnError] (F (M.Map Ident) a)) Void
  run (e :? xs) = Left (either (fmap pure) (checkNode' f) e) :? map (fmap pure) xs
    
checkNodeA
  :: Applicative f
  => (Ident -> DefnError)
  -> Node (f (Collect [DefnError] a))
  -> f (Collect [DefnError] (F (M.Map Ident) a))
checkNodeA f (Node k) = (checkNodeA' f . k) (fmap runA) where
  runA
    :: Applicative f
    => ChkStmts
      (f (Collect [DefnError] a))
      (M.Map Ident (ChkStmts (f (Collect [DefnError] (F (M.Map Ident) a))) Void))
    -> ChkStmts (f (Collect [DefnError] (F (M.Map Ident) a))) Void
  runA (e :? xs) =
    Left (either (fmap (fmap pure)) (checkNodeA' f) e) :? map (fmap (fmap pure)) xs
      
  checkNodeA' f = fmap (checkNode' f) . traverse (bitraverse id pure)
    
checkNode'
  :: (Ident -> DefnError)
  -> M.Map Ident (ChkStmts (Collect [DefnError] (F (M.Map Ident) a)) Void)
  -> Collect [DefnError] (F (M.Map Ident) a)
checkNode' f m = M.traverseWithKey
  (\ i c -> checkStmts (f i) (vacuous c) <&> either id absurd)
  m <&> wrap
  
checkMaybeNode
  :: (Ident -> DefnError)
  -> Node (Maybe (Collect [DefnError] a))
  -> Collect [DefnError] (F (M.Map Ident) a)
checkMaybeNode f (Node k) =
  (checkMaybeNode' f . k . fmap) (\ (e :? xs) ->
    Left (either (fmap (fmap pure)) (Just . checkMaybeNode' f) e) :? map (fmap (fmap pure)) xs)
  where
    checkMaybeNode'
      :: (Ident -> DefnError)
      -> M.Map Ident (ChkStmts (Maybe (Collect [DefnError] (F (M.Map Ident) a))) Void)
      -> Collect [DefnError] (F (M.Map Ident) a)
    checkMaybeNode' f m = traverseMaybeWithKey
      (\ i c -> checkMaybeStmts (f i) (vacuous c) <&> fmap (either id absurd))
      m <&> wrap
      

intro :: a -> Path -> M.Map Ident (ChkStmts a (Node a))
intro a (Path i maybe) =
  M.singleton i (maybe (Left a) (Right . fixNode . intro a) :? [])
  
instance Functor Node where
  fmap f (Node g) = Node (\ k -> g (k . M.map (first f)))
    
instance Semigroup (Node a) where
  f <> g = fixNode (M.unionWith (<>) (unfixNode f) (unfixNode g))
  
-- | The lhs of an assignment is a single name or a name and nested lhs. Second field 
-- is equivalent to Church-encoded 'Maybe p'.
data Path = Path Ident (forall x p . S.RelPath p => x -> (p -> x) -> x)

toPath :: Path -> P.Path Ident
toPath (Path i p) = p (S.local_ i) (S.#. i)

fromPath :: P.Path Ident -> Path
fromPath (P.Pure i) = S.local_ i
fromPath (P.Free (p `P.At` P.K_ i)) = fromPath p S.#. i

instance Show Path where
  showsPrec d p = showParen (d > 10)
    (showString "fromPath " . showsPrec 11 (toPath p))

instance S.Self Path where self_ i = Path i (\ nothing _ -> nothing)
instance S.Local Path where local_ i = Path i (\ nothing _ -> nothing)
  
instance S.Field Path where
  type Compound Path = Path
  Path i maybe #. k = Path i (\ _ just -> just (maybe (S.self_ k) (S.#. k)))

    

-- | A top-level set of tuple block statements, with pun statement desugaring.
newtype ChkTup a = ChkTup (M.Map Ident (ChkStmts a (Node a)))
  deriving Show
  
checkTup
  :: ChkTup (Collect [DefnError] a)
  -> Collect [DefnError] (M.Map Ident (F (M.Map Ident) a))
checkTup (ChkTup m) = M.traverseWithKey
  (\ i c -> checkStmts (f i) (checkNode f <$> c) <&> either pure id)
  m where
    f = OlappedSet . P.Pub . P.Pure . P.K_
    
-- | A decomposition pattern definition represents a decomposition of a value and assignment of parts.
-- Decomposed paths are checked for overlaps, and leaf 'let' patterns can be collected
-- and returned in pattern traversal order via the applicative wrapper.
checkDecomp
  :: Applicative f
  => ChkTup (f (Collect [DefnError] a))
  -> f (Collect [DefnError] (M.Map Ident (F (M.Map Ident) a)))
checkDecomp (ChkTup m) = getCompose (M.traverseWithKey
  (\ i c -> Compose (bitraverse id (checkNodeA f) c <&> (\ c -> 
    checkStmts (f i) c <&> either pure id)))
  m)
  where
    f = OlappedMatch . P.Pure . P.K_

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun :: S.Let s => Pun (S.Lhs s) (S.Rhs s) -> s
pun (Pun p a) = p S.#= a

instance (S.Self p, S.Self a) => S.Self (Pun p a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance (S.Self p, S.Local a) => S.Local (Pun p a) where
  local_ i = Pun (S.self_ i) (S.local_ i)

instance (S.Field p, S.Field a) => S.Field (Pun p a) where
  type Compound (Pun p a) = Pun (S.Compound p) (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

instance S.Self a => S.Self (ChkTup a) where self_ i = pun (S.self_ i)
instance S.Local a => S.Local (ChkTup a) where local_ i = pun (S.local_ i)

instance S.Field a => S.Field (ChkTup a) where
  type Compound (ChkTup a) = Pun Path (S.Compound a)
  p #. k = pun (p S.#. k)

instance S.Let (ChkTup a) where
  type Lhs (ChkTup a) = Path
  type Rhs (ChkTup a) = a
  p #= a = ChkTup (intro a p)

instance S.Sep (ChkTup a) where
  ChkTup m1 #: ChkTup m2 = ChkTup (M.unionWith (<>) m1 m2)
instance S.Splus (ChkTup a) where empty_ = ChkTup M.empty


-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value,
-- indicating that the path is to be checked for ambiguity but not assigned a value.
data Rec a = Rec { local :: M.Map Ident a, public :: M.Map Ident a }
--  deriving Functor
  
  
introVis :: a -> P.Vis Path Path -> Rec (ChkStmts a (Node a))
introVis a (P.Pub p) = Rec{local=M.empty,public=(intro a p)}
introVis a (P.Priv p) = Rec{local=(intro a p),public=M.empty}

instance Semigroup a => Semigroup (Rec a) where
  Rec{local=l1,public=s1} <> Rec{local=l2,public=s2} =
    Rec{local=(M.unionWith (<>) l1 l2),public=(M.unionWith (<>) s1 s2)}
  
instance Semigroup a => Monoid (Rec a) where
  mempty = Rec{local=M.empty,public=M.empty}
  mappend = (<>)


-- | Recursive block with destructing pattern assignments. 
data ChkRec f a = ChkRec [f (Maybe a)]

decl :: s -> ChkRec ((,) [s]) a
decl p = ChkRec [([p], Nothing)]

buildRec
  :: ChkRec ((,) [P.Vis Path Path]) a
  -> (Rec (ChkStmts (Maybe Int) (Node (Maybe Int))), [a], [Ident])
buildRec (ChkRec ps) = (r, pas, ns) where
  pas = mapMaybe snd ps
  (r, ns) = foldMap (\ (mb, s) -> (introVis mb s, pure (name s))) (enumerate ps)
  
  name :: P.Vis Path Path -> Ident
  name (P.Pub (Path i _)) = i
  name (P.Priv (Path i _)) = i
  
  enumerate :: [([a], Maybe b)] -> [(Maybe Int, a)]
  enumerate ps = concat (evalState (traverse enumeratePair ps) 0) where 
    enumeratePair (xs, Just _) = 
      traverse (\ a -> state (\ i -> ((Just i, a), i+1))) xs
    enumeratePair (xs, Nothing) = pure (map ((,) Nothing) xs)


checkRec
  :: Rec (ChkStmts (Maybe Int) (Node (Maybe Int)))
  -> Collect [DefnError] (Rec (F (M.Map Ident) Int))
checkRec (Rec{ local = l, public = s }) =
  checkVis (M.intersectionWith (,) l s) *> liftA2 Rec
    (checkDefns fl l)
    (checkDefns fs s)
  where
    fl = OlappedSet . P.Priv . P.Pure
    fs = OlappedSet . P.Pub . P.Pure . P.K_
  
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    checkVis = M.traverseWithKey (const . collect . pure . OlappedVis)
    checkDefns f = traverseMaybeWithKey (\ i s -> checkMaybeStmts
      (f i)
      (liftStmts s) <&> fmap (either id id))
          
    liftStmts
      :: ChkStmts (Maybe a) (Node (Maybe a))
      -> ChkStmts (Maybe (Collect [DefnError] (F (M.Map Ident) a)))
        (Maybe (Collect [DefnError] (F (M.Map Ident) a)))
    liftStmts = bimap
      (fmap (pure . pure))
      (Just . checkMaybeNode fs . fmap (fmap pure))
    

instance S.Self s => S.Self (ChkRec ((,) [s]) a) where self_ i = decl (S.self_ i)
instance S.Field s => S.Field (ChkRec ((,) [s]) a) where
  type Compound (ChkRec ((,) [s]) a) = S.Compound s
  p #. i = decl (p S.#. i)

instance (Applicative f, S.Patt (f p)) => S.Let (ChkRec f (p, a)) where
  type Lhs (ChkRec f (p, a)) = f p
  type Rhs (ChkRec f (p, a)) = a
  fp #= a = ChkRec [fp <&> (\ p -> Just (p ,a))]

instance S.Sep (ChkRec f a) where ChkRec xs #: ChkRec ys = ChkRec (xs <> ys)
instance S.Splus (ChkRec f a) where empty_ = ChkRec mempty
    

-- | Validate that a set of names are unambiguous, or introduces 'OlappedSet' errors for
-- ambiguous names.
checkStmts
  :: DefnError
  -> ChkStmts (Collect [DefnError] a) (Collect [DefnError] b)
  -> Collect [DefnError] (Either a b)
checkStmts _ (e :? []) = bisequenceA e
checkStmts d (e :? xs) = collect (pure d) *>
  sequenceA xs *> bisequenceA e
    

checkMaybeStmts
  :: DefnError
  -> ChkStmts (Maybe (Collect [DefnError] a)) (Maybe (Collect [DefnError] b))
  -> Collect [DefnError] (Maybe (Either a b))
checkMaybeStmts _ (e :? []) =
  getCompose (bitraverse (Compose . sequenceA) (Compose . sequenceA) e)
checkMaybeStmts d (e :? xs) =
  collect (pure d)
    *> getCompose (traverse (Compose . sequenceA) xs)
    *> getCompose (bitraverse (Compose . sequenceA) (Compose . sequenceA) e)

