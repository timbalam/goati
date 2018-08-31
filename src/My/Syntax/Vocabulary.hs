{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | The '[DefnError]' type implements an abstract interpretation for validating sets of 
-- definitions made using the syntax classes for duplicated names, overlapping definitions, 
-- etc. 
module My.Syntax.Vocabulary
  ( DefnError(..), Rec(..)
  , ChkDecomp(..), ChkTup(..), checkTup
  , ChkRec(..), checkRec, buildRec
  , Node(..), checkNode
  , Path(..), ChkStmts(..)
  )
  where

import qualified My.Types.Parser as P
import My.Types.Repr (Ident)
import My.Types.Classes (MyError(..))
import qualified My.Types.Syntax.Class as S
import My.Util (Collect(..), collect, (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free.Church (MonadFree(..), F(..))
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
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
data ChkStmts a s = Either a s :? [a]
infixr 5 :?

instance Functor (ChkStmts a) where
  fmap f (e :? xs) = fmap f e :? xs
  
{-
instance Applicative (ChkStmts a) where
  pure s = Right s :? []
  
  e       :? xs <*> Left y  :? ys = e           :? (xs ++ (y:ys))
  Left x  :? xs <*> e       :? ys = e           :? x : (xs ++ ys)
  Right f :? xs <*> Right a :? ys = Right (f a) :? (xs ++ ys)
-}

instance Semigroup s => Semigroup (ChkStmts a s) where
  (e       :? xs) <> (Left y  :? ys) = e              :? (xs ++ (y:ys))
  (Left x  :? xs) <> (e       :? ys) = e              :? x : (xs ++ ys)
  (Right a :? xs) <> (Right b :? ys) = Right (a <> b) :? (xs ++ ys)
  
instance Bifunctor ChkStmts where
  bimap f g (e :? xs) = bimap f g e :? fmap f xs
  
instance Bifoldable ChkStmts where
  bifoldMap f g (e :? xs) = bifoldMap f g e `mappend` foldMap f xs
  
instance Bitraversable ChkStmts where
  bitraverse  f g (e :? xs) = liftA2 (:?) (bitraverse f g e) (traverse f xs)
  
-- | Set of internal node statements sorted by name, represented as an unfold over nested
-- statements.
newtype Node a = Node { unfixNode ::
  forall x. Semigroup x => (M.Map Ident (ChkStmts a x) -> x) -> x  }

fixNode :: M.Map Ident (ChkStmts a (Node a)) -> Node a
fixNode m = Node (\ k -> k (fmap (fmap (`unfixNode` k)) m))

checkNode :: Node (Collect [DefnError] a) -> Collect [DefnError] (F (M.Map Ident) a)
checkNode (Node k) =
  (checkNode' . k . fmap) (\ (e :? xs) ->
    Left (either (fmap pure) checkNode' e) :? map (fmap pure) xs)
  where
    checkNode'
      :: M.Map Ident (ChkStmts (Collect [DefnError] (F (M.Map Ident) a)) Void)
      -> Collect [DefnError] (F (M.Map Ident) a)
    checkNode' m = M.traverseWithKey
      (\ i c -> checkStmts i (vacuous c) <&> either id absurd)
      m <&> wrap
  
checkMaybeNode
  :: Node (Maybe (Collect [DefnError] a)) -> Collect [DefnError] (F (M.Map Ident) a)
checkMaybeNode (Node k) =
  (checkMaybeNode' . k . fmap) (\ (e :? xs) ->
    Left (either (fmap (fmap pure)) (Just . checkMaybeNode') e) :? map (fmap (fmap pure)) xs)
  where
    
    checkMaybeNode'
      :: M.Map Ident (ChkStmts (Maybe (Collect [DefnError] (F (M.Map Ident) a))) Void)
      -> Collect [DefnError] (F (M.Map Ident) a)
    checkMaybeNode' m = M.traverseMaybeWithKey
      (\ i c -> checkMaybeStmts i (vacuous c) <&> fmap (either id absurd))
      m <&> wrap
      

intro :: a -> Path -> M.Map Ident (ChkStmts a (Node a))
intro a (Path i maybe) =
  M.singleton i (maybe (Left a) (Right . fixNode . intro a) :? [])
  
instance Functor Node where
  fmap f (Node g) = Node (\ k -> g (k . M.map (first f)))
    
instance Semigroup (Node a) where
  Node f <> Node g = Node (\ k ->
    f (\ m1 ->
    g (\ m2 ->
    k (M.unionWith (<>) m1 m2))))
  
-- | The lhs of an assignment is a single name or a name and nested lhs. Second field 
-- is equivalent to Church-encoded 'Maybe p'.
data Path = Path Ident (forall x p . S.RelPath p => x -> (p -> x) -> x)

instance S.Self Path where self_ i = Path i (\ nothing _ -> nothing)
instance S.Local Path where local_ i = Path i (\ nothing _ -> nothing)
  
instance S.Field Path where
  type Compound Path = Path
  Path i maybe #. k = Path i (\ _ just -> just (maybe (S.self_ k) (S.#. k)))

    

-- | A top-level set of tuple block statements, with pun statement desugaring.
newtype ChkTup a = ChkTup (M.Map Ident (ChkStmts a (Node a)))
  
checkTup
  :: ChkTup (Collect [DefnError] a)
  -> Collect [DefnError] (M.Map Ident (F (M.Map Ident) a))
checkTup (ChkTup m) = M.traverseWithKey
  (\ i c -> checkStmts i (checkNode <$> c) <&> either pure id)
  m

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
  deriving Functor
  
  
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
  (_, r, pas, ns) = foldr acc (0, mempty, mempty, mempty) ps

  acc
    :: ([P.Vis Path Path], Maybe a)
    -> (Int, Rec (ChkStmts (Maybe Int) (Node (Maybe Int))), [a], [Ident])
    -> (Int, Rec (ChkStmts (Maybe Int) (Node (Maybe Int))), [a], [Ident])
  acc (xs, Just v) (i, r, vs, ns) = (i', r', v:vs, ns') where
    (i', r', ns') = foldr
      (\ s (i, r, ns) -> (i+1, introVis (Just i) s <> r, name s:ns))
      (i, r, ns)
      xs
  acc (xs, Nothing) (i, r, cs, ns) = (i, r', cs, ns') where
    (r', ns') = foldr (\ s (r, ns) -> (introVis Nothing s <> r, name s:ns)) (r, ns) xs   

  name :: P.Vis Path Path -> Ident
  name (P.Pub (Path i _)) = i
  name (P.Priv (Path i _)) = i
  

{-
abs :: Ord k => M.Map k (Repr k a) -> Open k (Repr k) a
abs m = Abs pas [] m' where
  (pas, m') = traverse (\ (i, e) -> ([(Bind, lift e)], return i)) (enumerate m)
  where
    enumerate :: Ord k => M.Map k a -> M.Map k (Int, a)
    enumerate m = evalState (traverse (\ a -> state (\ i -> ((i, a), i+1))) m) 0
-}  


checkRec
  :: Rec (ChkStmts (Maybe Int) (Node (Maybe Int)))
  -> Collect [DefnError] (Rec (F (M.Map Ident) Int))
checkRec (Rec{ local = l, public = s }) =
  checkVis (M.intersectionWith (,) l s) *> liftA2 Rec (checkDefns l) (checkDefns s)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    checkVis = M.traverseWithKey (const . collect . pure . OlappedVis)
    checkDefns = M.traverseMaybeWithKey (\ i s ->
      checkMaybeStmts i (liftStmts s) <&>
          fmap (either id id))
          
    liftStmts
      :: ChkStmts (Maybe a) (Node (Maybe a))
      -> ChkStmts (Maybe (Collect [DefnError] (F (M.Map Ident) a)))
        (Maybe (Collect [DefnError] (F (M.Map Ident) a)))
    liftStmts = bimap
      (fmap (pure . pure))
      (Just . checkMaybeNode . fmap (fmap pure))
    

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


-- | A wrapped tuple with an additional applicative effect
newtype ChkDecomp f a = ChkDecomp (f (ChkTup a))

instance (Applicative f, S.Self (f a)) => S.Self (ChkDecomp f a) where self_ i = pun (S.self_ i)
instance (Applicative f, S.Local (f a)) => S.Local (ChkDecomp f a) where local_ i = pun (S.local_ i)
instance (Applicative f, S.Field (f a)) => S.Field (ChkDecomp f a) where
  type Compound (ChkDecomp f a) = Pun Path (S.Compound (f a))
  p #. i = pun (p S.#. i)
  
instance Applicative f => S.Let (ChkDecomp f a) where
  type Lhs (ChkDecomp f a) = Path
  type Rhs (ChkDecomp f a) = f a
  p #= fa = ChkDecomp ((p S.#=) <$> fa)
  
instance Applicative f => S.Sep (ChkDecomp f a) where
  ChkDecomp f #: ChkDecomp g = ChkDecomp (liftA2 (S.#:) f g)
  
instance Applicative f => S.Splus (ChkDecomp f a) where
  empty_ = ChkDecomp (pure S.empty_)
    

-- | Validate that a set of names are unambiguous, or introduces 'OlappedSet' errors for
-- ambiguous names.
checkStmts
  :: Ident
  -> ChkStmts (Collect [DefnError] a) (Collect [DefnError] b)
  -> Collect [DefnError] (Either a b)
checkStmts i (e :? []) = bisequenceA e
checkStmts i (e :? xs) = (collect . pure . OlappedSet . P.Pub . P.Pure) (P.K_ i) *>
  sequenceA xs *> bisequenceA e
    

checkMaybeStmts
  :: Ident
  -> ChkStmts (Maybe (Collect [DefnError] a)) (Maybe (Collect [DefnError] b))
  -> Collect [DefnError] (Maybe (Either a b))
checkMaybeStmts i (e :? []) =
  getCompose (bitraverse (Compose . sequenceA) (Compose . sequenceA) e)
checkMaybeStmts i (e :? xs) =
  (collect . pure . OlappedSet . P.Pub . P.Pure) (P.K_ i)
    *> getCompose (traverse (Compose . sequenceA) xs)
    *> getCompose (bitraverse (Compose . sequenceA) (Compose . sequenceA) e)

