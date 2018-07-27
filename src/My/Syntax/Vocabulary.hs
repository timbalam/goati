{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Validate syntactic block name hierarchies
module My.Syntax.Vocabulary
  ( E
  , runE
  , BlockBuilder(..)
  , DefnError(..)
  , buildBlock
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr
import My.Types.Classes (MyError(..))
import My.Types.Interpreter (K)
import qualified My.Types.Syntax.Class as S
import qualified My.Syntax.Import as S (Deps(..))
import My.Util
import Control.Applicative (liftA2, liftA3, Alternative(..))
import Control.Monad.Trans (lift)
import Control.Monad (ap)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.Foldable (fold, toList)
import Data.Semigroup
import Data.Functor.Plus (Plus(..), Alt(..))
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Typeable
import Data.List (elemIndex, nub)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void
import GHC.Exts (IsString(..))
import Control.Monad.Free
--import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Bound.Scope (abstractEither, abstract)


-- | Errors from binding definitions
data DefnError =
    OlappedMatch (P.Path P.Key)
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet P.VarPath
  -- ^ Error if a Block assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately
  deriving (Eq, Show, Typeable)
  
  
instance MyError DefnError where
  displayError (OlappedMatch p) = "Ambiguous destructuring of path " ++ show p
  displayError (OlappedSet p) = "Ambiguous assignment to path " ++ show p
  displayError (OlappedVis i) = "Variable assigned with multiple visibilities " ++ show i

  
-- | Wrapper for applicative syntax error checking
newtype E a = E (Collect [DefnError] a)
  deriving (Functor, Applicative)
  
runE :: E a -> Either [DefnError] a
runE (E e) = getCollect e

instance Semigroup a => Semigroup (E a) where
  (<>) = liftA2 (<>)
  
instance Monoid a => Monoid (E a) where
  mempty = pure mempty
  mappend = liftA2 mappend
  
instance S.Self a => S.Self (E a) where
  self_ = pure . S.self_
  
instance S.Local a => S.Local (E a) where
  local_ = pure . S.local_
  
instance S.Field a => S.Field (E a) where
  type Compound (E a) = E (S.Compound a)
  
  e #. k = e <&> (S.#. k)

instance Num a => Num (E a) where
  fromInteger = pure . fromInteger
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  
instance Fractional a => Fractional (E a) where
  fromRational = pure . fromRational 
  (/) = liftA2 (/)
  
instance IsString a => IsString (E a) where
  fromString = pure . fromString
  
instance S.Lit a => S.Lit (E a) where
  unop_ op = fmap (S.unop_ op)
  binop_ op a b = liftA2 (S.binop_ op) a b
  
    
-- | Validate that a finished tree has unambiguous paths and construct 
-- an expression that reflects the tree of assigned values.
--
-- If there are any ambiguous paths, returns them as list of 'OlappedSet'
-- errors.
--
-- Paths with missing 'Nothing' values represent paths that must not be assigned
-- and are not included in the constructed 'Node'.
--
-- Nested definitions shadow the corresponding 'Super' bound definitions ones on
-- a path basis - e.g. a path declared x.y.z = ... will shadow the .z component of
-- the .y component of the x variable. 
disambigpub, disambigpriv
  :: Ord k => M.Map Ident (An (Maybe (E a)))
  -> E (M.Map Ident (Open (Tag k) a))
disambigpub = disambig (OlappedSet . P.Pub . fmap P.K_)
diambigpriv = disambig (OlappedSet . P.Priv)

disambig
  :: (Ord k, MonadFree (M.Map Ident) m)
  => (P.Path Ident -> DefnError)
  -> M.Map Ident (Amb (Maybe (E b)))
  -> E (M.Map Ident (m b))
disambig f m = E (M.traverseMaybeWithKey (go . Pure) m)
  where
    go _ (Or a Nothing) = fmap pure <$> a
    go p (Or a (Just b)) = (collect . pure) (f p) *> go p b
    go p (Unamb m) = wrap
        <$> M.traverseMaybeWithKey (go (Free . P.At p . P.K_)) m

    
-- | Abstract builder for a 'group'
data Builder k group = B_
  { size :: Int
    -- ^ number of values to assign / paths
  , build :: forall a . [a] -> group a
    -- ^ builder function that performs assignment
  , names :: [k]
    -- ^ list of top-level names in assignment order
  }
  
instance Alt group => Semigroup (Builder group) where
  B_ sz1 b1 n1 <> B_ sz2 b2 n2 =
    B_ (sz1 + sz2) b (n1 <> n2)
    where
      b :: forall a . [a] -> group a
      b xs = let (x1, x2) = splitAt sz1 xs in b1 x1 <!> b2 x2
  
instance Plus group => Monoid (Builder group) where
  mempty = B_ 0 (const zero) mempty
  mappend = (<>)
  
hoistBuilder :: (forall x . g x -> f x) -> Builder g -> Builder f
hoistBuilder f (B_ sz b n) = B_ sz (f . b) n

    
-- | A 'Path' is a sequence of fields
data Path k =
  PathB
    (forall a. Amb a -> (Ident, Amb a))
    -- ^ push additional fields onto path
    k
    -- ^ top-level field name

instance S.Self k => S.Self (Path k) where self_ i = PathB (i,) (S.self_ i)
  
instance S.Local k => S.Self (Path k) where local_ i = PathB (i,) (S.local_ i)
  
instance S.Field (Path k) where
  type Compound (Path k) = Path k
  PathB f k #. i = PathB (f . wrap . M.singleton i) k
    
-- | A set of paths possibly with associated values of type 'a'
newtype Paths a = Paths { unPaths :: M.Map Ident (Amb (Maybe a)) }
  deriving Functor
  
instance Alt Paths where Paths m1 <!> Paths m2 = Paths (M.unionWith (<!>) m1 m2)

instance Plus Paths where zero = Paths M.empty

intro :: Path k -> Builder k Paths
intro (PathB f k) =
  B_ 1 (Paths . uncurry M.singleton . f . pure . Just . head) [k]
  
instance S.Self k => S.Self (Builder k Paths) where
  self_ i = intro (S.self_ i)
  
instance S.Local k => S.Local (Builder k Paths) where
  local_ i = intro (S.local_ i)
  
instance S.Field (Builder k Paths) where
  Compound (Builder k Paths) = Path k
  p #. k = intro (p #. k)


-- | A punned assignment statement
data Pun = Pun (forall a . S.RelPath a => a) (forall a. S.VarPath a => a)

instance S.Self Pun where self_ i = Pun (S.self_ i) (S.Self_ i)

instance S.Local Pun where local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field Pun where
  S.Compound Pun = Pun
  Pun p a #. k = Pun (p #. k) (a #. k)

-- | A 'Tuple' is a group of paths with associated values
data TupBuilder a = TupB (Builder Ident Paths) [a] -- ^ values in assignment order
  
pun :: S.VarPath a => Pun -> TupBuilder a
pun (Pun p a) = TupB p [a]
  
instance S.Self a => S.Self (TupBuilder a) where self_ i = pun (S.self_ i)
  
instance S.Local a => S.Local (TupBuilder a) where local_ i = pun (S.local_ i)
  
instance S.Field a => S.Field (TupBuilder a) where
  type Compound (TupBuilder a) = Pun (S.Compound a)
  pb #. k = pun (pb S.#. k)
  
instance S.Let (TupBuilder a) where
  type Lhs (TupBuilder a) = Builder Ident Paths
  type Rhs (TupBuilder a) = a
  b #= a = TupB b [a]
    
instance S.Sep (TupBuilder a) where 
  TupB g1 a1 #: TupB g2 a2 = TupB (g1 <> g2) (a1 <> a2)
    
instance S.Splus (TupBuilder a) where
  empty_ = TupB mempty mempty
  
    
-- | Validate that a group of private/public definitions are disjoint, and
--   extract 'Node' expressions for each defined name.
validatevis
  :: Ord k => VisPaths x
  -> Collect [DefnError]
    ( M.Map Ident (Open (Tag k) (Bind Ident x))
    , M.Map Ident (Open (Tag k) (Bind Ident x))
    )
validatevis v = viserrs *> liftA2 (,) (validatepriv locn) (validatepub pubn)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    viserrs = M.foldrWithKey
      (\ l (a, b) e -> e *> (collect . pure) (OlappedVis l))
      (pure ())
      (M.intersectionWith (,) locn pubn)
      
    locn = unPaths (local v)
    pubn = unPaths (self v)


-- | Paths partitioned by top-level visibility
data VisPaths a = VisPaths { local :: Paths a, self :: Paths a }
  deriving Functor

instance Alt VisPaths where
  VisPaths l1 s1 <!> VisPaths l2 s2 = VisPaths (l1 <!> l2) (s1 <!> s2)

instance Plus VisPaths where
  zero = VisPaths zero zero
    
introVis :: P.Vis Path Path -> Builder VisPaths
introVis (P.Priv p) = hoistBuilder (\ b -> zero {local = b}) (intro p)
introVis (P.Pub p) = hoistBuilder (\ b -> zero {self = b}) (intro p)


-- | A set of assignment and corresponding extraction paths
data DecompBuilder = DecompB
  (Builder Ident Paths)
  (forall a . S.RelPath a => [(a, Patt)])
  
decompPun :: Pun -> DecompBuilder
decompPun (Pun r a) = DecompB (intro r) [(r, a)]
  
instance S.Self DecompBuilder where self_ i = decompPun (S.self i)

instance S.Local DecompBuilder where local_ i = decompPun (S.local i)

instance S.Field DecompBuilder where
  type Compound DecompBuilder = Pun
  p #. k = decompPun (p #. k)
  
instance S.Let DecompBuilder where
  type Lhs DecompBuilder = Pun
  type Rhs DecompBuilder = Patt
  Pun r _ #= p = DecompB r [(r, p)]
  
instance S.Sep DecompBuilder where
  DecompB g1 v1 #: DecompB g2 v2 = DecompB (g1 <> g2) (v1 <> v2)
  
instance S.Splus DecompBuilder where
  empty_ = DecompBuilder mempty mempty
    
    
-- | A pattern represents decomposing a value and assignment of distinct parts
data Patt =
  PattB
    (Builder (P.Vis Ident Ident) Paths)
      -- ^ Paths assigned to parts of the pattern
    (E [Extract])
      -- ^ Value deconstructors
      
instance Semigroup Patt where
  PattB g1 v1 <> PattB g2 v2 = PattB (g1 <> g2) (v1 <> v2)
  
instance Monoid Patt where
  mempty = PattB mempty mempty
  mappend = (<>)
  
letpath :: Path (P.Vis Ident Ident) -> Patt
letpath p = PattB (intro p) d
  where
    d = B_ 1 (pure . pure . head) []

ungroup :: DecompBuilder -> Patt
ungroup (DecompB g ps) = PattB pg (pe $> derrs) where
  PattB pg pe = foldMap (\ (f, PattB g e) -> PattB g (fmap (f <>) <$> e)) ps
  
  derrs :: E (Free (M.Map Ident) ())
  derrs = (disambigmatch . unpaths . build g) (repeat ())
  
  
newtype Extract = Extract { extract :: forall a . Path a => a -> a }

instance Semigroup Extract where
  Extract f <> Extract g = Extract (f . g)

instance S.Self Extract where self_ i = Extract (#. i)

instance S.Field Extract where
  type Compound Extract = Extract
  Extract f #. i = Extract ((#. i) . f)

  
disambigmatch = disambig (OlappedMatch . fmap K_)
  
  
instance S.Self Patt where self_ i = letpath (S.self_ i)
  
instance S.Local Patt where local_ i = letpath (S.local_ i)
  
instance S.Field Patt where
  type Compound Patt = Path (P.Vis Ident Ident)
  v #. k = letpath (v S.#. k)

type instance S.Member Patt = Patt

instance S.Tuple Patt where
  type Tup Patt = TupBuilder Patt
  tup_ g = ungroup g
  
instance S.Extend Patt where
  type Ext Patt = Patt
  PattB g1 d1 # PattB g2 d2 = PattB (g1 <> g2) (d1 <> d2)
    
    
    

-- | An ungroup pattern
data Ungroup =
  Ungroup
    PattBuilder
    -- ^ Builds the set of local and public assignments made by rhs patterns, where
    -- assigned values are obtained by deconstructing an original value
    [Ident]
    -- ^ List of fields of the original value used to obtain deconstructed values    
    

letungroup :: PattBuilder -> Ungroup -> PattBuilder
letungroup (PattB g1 v1) (Ungroup (PattB g2 v2) n) =
  PattB (g1 <> g2) (v1' <> v2)
    where
      -- left-hand pattern decomp function gets expression restricted to unused fields
      v1' :: forall k a . Ord k => E (Open (Tag k) a -> [Open (Tag k) a])
      v1' = (. rest) <$> v1
      
      rest :: Ord k => Open (Tag k) a -> Open (Tag k) a
      rest e = (Defn . hide (nub n) . selfApp) (lift e)

      -- | Folds over a value to find keys to restrict for an expression.
      --
      -- Can be used as function to construct an expression of the 'left-over' components
      -- assigned to nested ungroup patterns.
      hide :: Foldable f => f Ident -> Closed (Tag k) a -> Closed (Tag k) a
      hide ks e = foldl (\ e k -> e `Fix` Key k) e ks
    
    
-- | Build a recursive Block group
data BlockBuilder a = BlockB
  (Builder (P.Vis Ident Ident) Paths)
  (E [a])
  
decl :: Path Ident -> BlockBuilder a
decl (PathB f n) = BlockB g []
    where
      g = B_ {size=0, build=p, names=[P.Pub n]}
      
      p :: Paths a
      p = (Paths . M.singleton n . f) (pure Nothing)
    
instance S.Self (BlockBuilder a) where self_ k = decl (S.self_ k)
  
instance S.Field (BlockBuilder a) where
  type Compound (BlockBuilder a) = Path Ident
  b #. k = decl (b S.#. k)

instance Ord k => S.Let (BlockBuilder a) where
  type Lhs (BlockBuilder a) = PattBuilder
  type Rhs (BlockBuilder a) = E a
  PattB g e #= v = BlockB g (liftA2 (fmap extract) e v)
      
instance S.Sep (BlockBuilder a) where
  BlockB g1 v1 #: BlockB g2 v2 = BlockB (g1 <> g2) (v1 <> v2)
  
instance S.Splus (BlockBuilder a) where empty_ = BlockB mempty mempty
    
    
-- | Validate a nested group of matched paths are disjoint, and extract
-- a decomposing function
validatedecomp
  :: (S.Path a, Monoid b)
  => M.Map Ident (An (Maybe (E (a -> b))))
     -- ^ Matched paths to nested patterns
  -> E (a -> b)
     -- ^ Value decomposition function
validatedecomp = fmap pattdecomp . M.traverseMaybeWithKey (go . Pure . P.K_) where
  go _ (An a Nothing) = sequenceA a
  go p (An a (Just b)) = (E . collect . pure) (OlappedMatch p)
    *> sequenceA a *> go p b
  go p (Un ma) = Just . pattdecomp 
    <$> M.traverseMaybeWithKey (go . Free . P.At p . P.K_) ma
    
  -- | Unfold a set of matched fields into a decomposing function
  pattdecomp :: (S.Path a, Monoid b) => M.Map Ident (a -> b) -> (a -> b)
  pattdecomp = M.foldMapWithKey (\ k f a -> f (a S.#. k))

  
-- | Tree of paths with one or values contained in leaves and zero or more
--   in internal nodes
--
--   Semigroup and monoid instances defined will union subtrees recursively
--   and accumulate values.
data Amb a = a `Or` Maybe (Amb a) | Unamb (M.Map Ident (Paths a))
  deriving (Functor, Foldable, Traversable)
  
instance Applicative Amb where
  pure a = a `Or` Nothing
  (<*>) = ap
  
instance Monad Amb where
  return = pure
  
  a `Or` Nothing >>= k = k a
  a `Or` Just as >>= k = k a <!> (as >>= k)
  Unamb ma >>= k = Unamb ((>>= k) <$> ma)
  
instance MonadFree (M.Map Ident) Amb where
  wrap = Unamb
  
instance Alt Amb where
  x `Or` Just a <!> b = (Or x . Just) (a <!> b)
  x `Or` Nothing <!> b = x `Or` Just b
  a <!> x `Or` Nothing = x `Or` Just a
  a <!> x `Or` Just b = (Or x . Just) (a <!> b)
  Unamb ma <!> Unamb mb = Unamb (M.unionWith (<!>) ma mb)

