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
import My.Util (Collect(..), collect, (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free.Church (MonadFree(..), F)
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
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
newtype Check a = Check (Check a)
  deriving (Functor, Foldable, Traversable, Applicative)

instance S.Self a => S.Self (Check a) where self_ i = pure (S.self_ i)
instance S.Local a => S.Local (Check a) where local_ i = pure (S.local_ i)
  
instance S.Field a => S.Field (Check a) where
  type Compound (Check a) = Check (S.Compound a)
  c #. i = c <&> (S.#. i)

instance Num a => Num (Check a) where
  fromInteger = pure . fromInteger
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum

instance Fractional a => Fractional (Check a) where
  fromRational = pure . fromRational
  (/) = liftA2 (/)

instance IsString a => IsString (Check a) where
  fromString = pure . fromString

instance S.Lit a => S.Lit (Check a) where
  unop_ op = fmap (unop_ op) 
  binop_ op = liftA2 (binop_ op)


-- | A nested group of paths, represented by  the Church-encoded Free monad.
type G = F (M.Map Ident)
  
-- | A top-level block of assignments partitioned by visibility, with nested paths.
data Rec a = Rec { local :: M.Map Ident a, public :: M.Map Ident a }
  deriving Functor

instance S.Block (Check (Rec (G a))) where
  type Rec (Check (Rec (G a))) = ChkRec
    (Check (G a))
    (FixChk (Check (G a)))
  block_ s = checkRec (Just . checkFix wrap <$> s) <&> (\ (l,s) ->
    B (\ kp kf -> 
      (M.map (\ g -> runG g kp kf) l, M.map (\ g -> runG g kp kf) s)))
  
    
-- | A top-level tuple block.
newtype Tup a = Tup (M.Map Ident a)
  deriving (Functor, Foldable, Traversable)

instance S.Tuple (Check (Tup (G a))) where
  type Tup (Check (Tup (G a))) = ChkTup
    (Check (G a))
    (FixChk (Check (G a)))
  tup_ (Tup s) = checkStmts (checkFix wrap <$> s) <&> (\ m ->
    T (\ kp kf -> M.map (\ g -> runG g kp kf) m))
  
-- | A set of overlapping statements
data ChkStmts a s = Either a s :? [a]
infixr 5 :?

instance Functor (ChkStmts a) where
  fmap f (e :? xs) = fmap f e :? xs
  
instance Applicative (ChkStmts a) where
  pure s = Right s :? []
  
  e       :? xs <*> Left y  :? ys = e           :? (xs ++ (y:ys))
  Left x  :? xs <*> e       :? ys = e           :? x : (xs ++ ys)
  Right f :? xs <*> Right a :? ys = Right (f a) :? (xs ++ ys)
  
type Node = M.Map Ident
  
-- | The lhs of an assignment is a single name or a name and nested lhs. Second field 
-- is equivalent to Church-encoded 'Maybe p'.
data Path p = Path Ident (forall x . x -> (p -> x) -> x)
newtype SomePath = SomePath (forall p. S.RelPath p => Path p)
  
-- | Church-encoded fix-point for 'Map Ident :.: ChkStmts a'
newtype FixChk a = FixChk { unfixChk ::
  forall x. (S.Let x, S.Rhs x ~ a, S.Splus x) => (M.Map Ident (ChkStmts a x) -> x) -> x }
  
fixChk :: M.Map Ident (ChkStmts a (FixChk a)) -> FixChk a
fixChk c = FixChk (\ k -> k (fmap (`unfixChk` k) c))

instance S.Self (Path p) where self_ i = Path i (\ nothing _ -> nothing)
instance S.Local (Path p) where local_ i = Path i (\ nothing _ -> nothing)
instance S.Self SomePath where self_ i = SomePath (S.self_ i)
instance S.Local SomePath where local_ i = SomePath (S.local_ i)
  
instance (S.Self p, S.Field p) => S.Field (Path p) where
  type Compound (Path p) = Path (S.Compound p)
  Path i maybe #. k = Path i (\ _ just -> just (maybe (S.self_ k) (S.#. k)))
instance S.Field SomePath where
  type Compound SomePath = SomePath
  SomePath p #. i = SomePath (p S.#. i)
  
instance (S.Let s, S.Rhs s ~ a) => S.Let (Node (ChkStmts a s)) where
  type Lhs (Node (ChkStmts a s)) = Path (S.Lhs s)
  type Rhs (Node (ChkStmts a s)) = a
  Path i maybe #= a = M.singleton i (maybe (Left a) (\ p -> Right (p S.#= a)) :? [])
  
instance S.Let (FixChk a) where
  type Lhs (FixChk a) = SomePath
  type Rhs (FixChk a) = a
  SomePath p #= a = fixChk (p S.#= a)
  
instance S.Sep s => S.Sep (Node (ChkStmts a s)) where
  m1 #: m2 = M.unionWith (liftA2 (S.#:)) m1 m2
    
instance S.Sep (FixChk a) where
  FixChk f #: FixChk g = FixChk h where
    h :: S.Sep s => (Node (ChkStmts a s) -> s) -> s
    h k = f (\ s1 -> g (\ s2 -> k (s1 S.#: s2)))
    
instance S.Sep s => S.Splus (Node (ChkStmts a s)) where empty_ = M.empty
instance S.Splus (FixChk a) where empty_ = FixChk (\ k -> k S.empty_)


-- | A set of statements from a tuple block, including desugaring punned assignments.
data ChkTup s a = ChkTup (Builder GTup s) [a]
newtype GTup s a = GTup (Tup (ChkStmts a s))

instance S.Sep s => S.Sep (GTup s a) where
  GTup (Tup m1) #: GTup (Tup m2) = GTup (Tup (M.unionWith (#:) m1 m2))
  
instance S.Sep s => S.Splus (GTup s a) where empty_ = GTup (Tup M.empty)

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun :: (S.Let s, S.Lhs s ~ p, S.Rhs s ~ a) => Pun p a -> ChkTup s a
pun (Pun p a) = ChkTup (Builder { size=1, build = GTup . Tup . (p S.#=) . head }) [a] 

instance (S.Self p, S.Self a) => S.Self (Pun p a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance (S.Self p, S.Local a) => S.Local (Pun p a) where
  local_ i = Pun (S.self_ i) (S.local_ i)

instance (S.Field p, S.Field a) => S.Field (Pun p a) where
  type Compound (Pun p a) = Pun (S.Compound p) (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

instance (S.Let s, S.Self (S.Lhs s), S.Rhs s ~ a, S.Self a)
  => S.Self (ChkTup a s) where self_ i = pun (S.self_ i)
instance (S.Let s, S.Self (S.Lhs s), S.Rhs s ~ a, S.Local a)
  => S.Local (ChkTup a s) where local_ i = pun (S.local_ i)

instance (S.Let s, S.Path (S.Lhs s), S.Rhs s ~ a, S.Field a) => S.Field (ChkTup a s) where
  type Compound (ChkTup a s) = Pun (S.Lhs s) (S.Compound a)
  p #. k = pun (p S.#. k)

instance (S.Let s, S.Rhs s ~ a) => S.Let (ChkTup a s) where
  type Lhs (ChkTup a s) = Path (S.Lhs s)
  type Rhs (ChkTup a s) = a
  p #= a = ChkTup (Build { size=1, build = GTup . Tup . (p S.#=) . head }) [a]

instance S.Sep s => S.Sep (ChkTup a s) where
  ChkTup b1 v1 #: ChkTup b2 v2 = ChkTup (b1 <> b2) (v1 <> v2)
instance S.Sep s => S.Splus (ChkTup a s) where empty_ = ChkTup mempty mempty

-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value,
-- indicating that the path is to be checked for ambiguity but not assigned a value.
data ChkRec a s = ChkRec (Builder (GRec s)) (Check [a])

-- | Wrapper for a 'Rec' group with appropriate type arguments for 'Builder'.
-- Lifts the underlying 'S.Sep' implementation.
newtype GRec s a = GRec (Rec (ChkStmts (Maybe a) s))

instance S.Sep s => S.Sep (GRec s a) where
  GRec (Rec {local=l1,public=s1}) #: GRec (Rec {local=l2,public=s2}) =
    GRec (Rec { local = M.unionWith (S.#:) l1 l2, public = M.unionWith (S.#:) s1 s2 })
instance S.Sep s => S.Splus (GRec s a) where empty_ = GRec (Rec M.empty M.empty)

-- | Wrapped path assignment with additional ability to handle non-assigning 'decl' statements.
newtype FixDecl a = FixDecl { unfixDecl :: FixChk (Maybe a) }
  
fixDecl :: M.Map Ident (ChkStmts (Maybe a) (FixDecl a)) -> FixDecl a
fixDecl c = FixDecl (fixChk (coerce c))

-- | A decomposable value.
-- Equivalent to the Church-encoded free monad for 'M.Map Ident :.: Maybe'.
type U = F (Compose (M.Map Ident) Maybe)

  
decl :: Path s -> M.Map Ident (ChkStmts (Maybe a) s)
decl (Path i maybe) = M.singleton i (maybe (Left Nothing) Right :? [])
  
instance S.Self (Rec (ChkStmts (Maybe a) s)) where
  self_ i = Rec { patterns = [], local = M.empty, public = decl (S.self_ i) }
  
instance S.Self (FixDecl a) where self_ i = FixDecl (FixChk (\ k -> k (decl (S.self_ i))))
  
instance S.RelPath s => S.Field (Rec (ChkStmts (Maybe a) s)) where
  type Compound (Rec (ChkStmts (Maybe a) s)) = Path s
  p #. i = Rec { local = M.empty, public = decl (p S.#. i) }
  
instance S.Field (FixDecl a) where
  type Compound (FixDecl a) = SomePath
  SomePath p #. i = fixDecl (decl (p S.#. i))

instance S.Path a => S.Let (Rec p (ChkStmts a s)) where
  type Lhs (Rec p (ChkStmts (Maybe a) s)) = p
  type Rhs (Rec p (ChkStmts (Maybe a) s)) = a
  p #= a = Rec { patterns = [(p, a)], local = l, public = s }
  
instance S.Path a => S.Let (FixDecl a) where
  type Lhs (FixDecl a) = SomePath
  type Rhs (FixDecl a) = a
  SomePath p #= a = fixDecl (p S.#= pure a)

instance S.Sep s => S.Sep (ChkRec s a) where
  ChkRec b1 v1 #: ChkRec b2 v2 = ChkRec (b1 <> b2) (liftA2 (<>) v1 v2)

instance S.Sep s => S.Splus (Rec s) where
  empty_ = ChkRec mempty (pure mempty)


-- | A pattern definition represents the simultaneous decomposing a value into distinct
-- parts and the assignment of the parts
data ChkPatt s = ChkPatt
  (Builder (GRec s))
  (forall x. S.Path x => Check (U x -> [U x]))
  -- ^ head of passed list is 'left overs' from upstream patterns
  
-- | A pattern definition represents a decomposition of a value and assignment of parts.
-- Decomposed paths are checked for overlaps, and leaf 'let' patterns are returned in 
-- pattern traversal order.
newtype Patt p a = Patt { runPatt :: ([a], Check p)

letpath :: Pun (Check p) a -> Patt p a
letpath (Pun p a) = Patt p [a]

instance (S.Self p, S.Self a) => S.Self (Patt p a) where self_ i = letpath (S.self_ i)
instance (S.Self p, S.Local a) => S.Local (Patt p a) where local_ i = letpath (S.local_ i)
instance (S.Field p, S.Field a) => S.Field (Patt p a) where
  type Compound (Patt p a) = Pun (S.Compound p) (S.Compound a)
  p #. i = letpath (p S.#. i)
  
instance S.Tuple (Patt (G p) a) where
  type Tup (Patt (G p) a) =
    Tup (ChkStmts (Patt (G p) a) (FixChk (Patt (G p) a)))
  tup_ (Tup m) = Patt (traverse
    (\ (e :? xs) ->
      liftA2 (:?) (bitraverse runPatt fixPatt e) (traverse runPatt xs))
    m <&> (\ m -> checkNode (checkFix wrap <$> m) <&> wrap))
    where
      fixPatt :: FixChk (Patt (G p) a) -> Patt (FixChk (G p)) a
      fixPatt f = Patt (unfixChk f (\ m -> traverse
        (\ (e :? xs) -> 
          liftA2 (:?) (bitraverse runPatt id e) (traverse runPatt xs))
        m <&> fixChk))
          

instance S.Extend p => S.Extend (Patt (G p) a) where
  type Ext (Patt (G p) a) = Patt (G p) a
  Patt p1 # Patt p2 = Patt (liftA2 (liftA2 ext) p1 p2) where
    ext f g = G (\ kp kf -> 
    
  
letpath
  :: (forall x. S.RelPath x => P.Vis (Path x) (Path x)) -> ChkPatt s
letpath v = ChkPatt (f . head) (pure id) where
  f a = case v of
    P.Pub p -> Rec { local = M.empty, public = p S.#= a }
    P.Priv p -> Rec { local = p S.#= a, public = M.empty }

instance S.Self SomeVisPath where self_ i = SomeVisPath (S.self_ i)
instance S.Local SomeVisPath where local_ i = SomeVisPath (S.local_ i)
instance S.Field SomeVisPath  where
  type Compound SomeVisPath = SomeVisPath
  SomeVisPath p #. i = SomeVisPath (p S.#. i)
 
instance S.Self (ChkPatt a) where self_ i = letpath (S.self_ i)
instance S.Local (ChkPatt a) where local_ i = letpath (S.local_ i)
  
instance S.Field (ChkPatt a) where
  type Compound (ChkPatt a) = SomeVisPath
  SomeVisPath v #. k = letpath (v S.#. k)

type instance S.Member (ChkPatt s) = ChkPatt s

instance S.Tuple (ChkPatt s) where
  type Tup (ChkPatt s) =
    Tup (ChkStmts (G (ChkPatt s)) (FixChk (G (ChkPatt s))))
  tup_ s = S.tup_ s <&> (\ (ChkDecomp k) -> ChkPatt (\ a -> appEndo (fst (k a)) S.empty_))

instance S.Tuple (ChkPatt s) where
  type Tup (ChkPatt s) =
    ChkTup (G (ChkPatt s)) (FixChk (G (ChkPatt s)))
  tup_ (ChkTup b v) = checkNode (checkFix wrap <$> m) <&> (\ m ->
    M.traverseWithKey
      (\ i g a -> let
        kp (ChkPatt build dest) = (build, pure ((a S.#. i) :))
        kf m = traverse Compose m <&> (\ m' -> 
        in runG g kp kf)
      m <&> wrap . Compose)


instance S.Extend (Check (ChkPatt s)) where
  type Ext (Check (ChkPatt s)) = Check (ChkDecomp s)
  (#) = liftA2 extend where
    extend :: ChkPatt s -> ChkDecomp s -> ChkPatt s
    extend (ChkPatt f) (ChkDecomp g) = ChkPatt (\ a -> let (Endo k, a') = g a in k (f a'))
  

  

-- | Validate that a set of names are unambiguous, or introduces 'OlappedSet' errors for
-- ambiguous names.
checkStmts
  :: Ident -> ChkStmts (Check a) (Check b) -> Check (Either a b)
checkStmts i (e :? []) = sequenceA e
checkStmts i (e :? xs) = (collect . pure . OlappedSet . P.Pub . P.Pure) (P.K_ i) *>
  sequenceA xs *> sequenceA e
    

checkStmtsF
  :: Applicative f => Ident -> ChkStmts (f (Check a)) (f (Check b)) -> Check (f (Either a b))
checkStmtsF i (e :? []) = traverse sequenceA e
checkStmtsF i (e :? xs) = (collect . pure . OlappedSet . P.Pub . P.Pure) (P.K_ i) *>
  traverse sequenceA xs *> traverse sequenceA e
    

checkNode :: M.Map Ident (Check a) (Check a) -> Check (M.Map Ident a)
checkNode = M.traverseWithKey (\ i s -> either id id <$> checkStmts i s)
          
checkFix
  :: (M.Map Ident a -> a) -> FixChk (Check a) -> Check a
checkFix k = flip unfixChk (fmap k . checkNode)


checkRec
  :: Rec (ChkStmts (Maybe (Check a)) (Maybe (Check a))) -> Check (Rec a)
checkRec (Rec{ local = l, public = s }) =
  checkVis (M.intersectionWith (,) l s) *> liftA2 Rec (checkLoc l) (checkPub s)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    checkVis = M.traverseWithKey (const . collect . pure . OlappedVis)
    checkLoc = M.traverseMaybeWithKey (\ i s -> fmap (either id id) <$> checkStmtsF i s)
    checkPub = M.traverseMaybeWithKey (\ i s -> fmap (either id id) <$> checkStmtsF i s)
   

-- | Build a group from a sequence of statements keeping track of assignment order.
data Builder group = Builder
  { size :: Int
  , build :: forall x . S.Splus (group x) => [x] -> group x
  }
  
instance Semigroup (Builder group) where
  Builder{size=sz1,build=b1} <> Builder{size=sz2,build=b2} =
    Builder { size = sz1 + sz2, build = b' } where
      b' xs = let (xs1, xs2) = splitAt sz1 xs in b1 xs1 S.#: b2 xs2
      
instance Monoid (Buider group) where
  mempty = Builder { size = 0, build = pure S.empty_ }
  mappend = (<>)

      
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

