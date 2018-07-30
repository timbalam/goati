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
  

    
-- | Abstract builder for a 'group'
data Builder k group = B_
  { size :: Int
    -- ^ number of values to assign / paths
  , build :: forall a . [a] -> group a
    -- ^ builder function that performs assignment
  , names :: [k]
    -- ^ list of top-level names in assignment order
  }
  
instance Alt group => Semigroup (Builder k group) where
  B_ sz1 b1 n1 <> B_ sz2 b2 n2 =
    B_ (sz1 + sz2) b (n1 <> n2)
    where
      b :: forall a . [a] -> group a
      b xs = let (x1, x2) = splitAt sz1 xs in b1 x1 <!> b2 x2
  
instance Plus group => Monoid (Builder k group) where
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
  
instance S.Local k => S.Local (Path k) where local_ i = PathB (i,) (S.local_ i)
  
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
  type Compound (Builder k Paths) = Path k
  p #. k = intro (p #. k)

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
  :: (Ord k, MonadFree (M.Map Ident) m) => Paths (E a) -> E (M.Map Ident (m a))
disambigpub = disambig (OlappedSet . P.Pub . fmap P.K_)
disambigpriv = disambig (OlappedSet . P.Priv)

disambig
  :: (Ord k, MonadFree (M.Map Ident) m)
  => (P.Path Ident -> DefnError) -> Paths (E a) -> E (M.Map Ident (m a))
disambig f (Paths m) = E (M.traverseMaybeWithKey (go . Pure) m)
  where
    go _ (Overlap a Nothing) = fmap pure <$> a
    go p (Overlap a (Just b)) = (collect . pure) (f p) *> go p b
    go p (Disjoint m) = wrap
        <$> M.traverseMaybeWithKey (go (Free . P.At p . P.K_)) m

-- | A punned assignment statement
data Pun = Pun (forall a . S.RelPath a => a) (forall a. S.VarPath a => a)

instance S.Self Pun where self_ i = Pun (S.self_ i) (S.self_ i)

instance S.Local Pun where local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field Pun where
  type Compound Pun = Pun
  Pun p a #. k = Pun (p #. k) (a #. k)

-- | A 'Tuple' is a group of paths with associated values
data TupBuilder a = TupB (Builder Ident Paths) [a] -- ^ values in assignment order

pun :: S.VarPath a => Pun -> TupBuilder a
pun (Pun p a) = TupB p [a]

instance S.Self a => S.Self (TupBuilder a) where self_ i = pun (S.self_ i)

instance S.Local a => S.Local (TupBuilder a) where local_ i = pun (S.local_ i)

instance S.Field a => S.Field (TupBuilder a) where
  type Compound (TupBuilder a) = Pun
  pb #. k = pun (pb S.#. k)

instance S.Let (TupBuilder a) where
  type Lhs (TupBuilder a) = Builder Ident Paths
  type Rhs (TupBuilder a) = a
  b #= a = TupB b [a]

instance S.Sep (TupBuilder a) where 
  TupB g1 a1 #: TupB g2 a2 = TupB (g1 <> g2) (a1 <> a2)

instance S.Splus (TupBuilder a) where
  empty_ = TupB mempty mempty

-- | Paths partitioned by top-level visibility
data VisPaths a = VisPaths { local :: Paths a, public :: Paths a }
  deriving Functor

instance Alt VisPaths where
  VisPaths l1 s1 <!> VisPaths l2 s2 = VisPaths (l1 <!> l2) (s1 <!> s2)

instance Plus VisPaths where
  zero = VisPaths zero zero
    
introVis :: Path (P.Vis Ident Ident) -> Builder VisPaths
introVis p@(PathB _ (P.Priv _)) = hoistBuilder (\ b -> zero {local = b}) (intro p) 
introVis p@(PathB _ (P.Pub _)) = hoistBuilder (\ b -> zero {public = b}) (intro p)

-- | Validate that a group of private/public definitions are disjoint.
disambigvis
  :: (Ord k, MonadFree (M.Map Ident) m)
  => VisPaths (E a)
  -> Collect [DefnError]
    ( M.Map Ident (m a)
    , M.Map Ident (m a)
    )
disambigvis (Paths {local=loc, public=pub}) = viserrs *> liftA2 (,) (disambigpriv loc) (disambigpub pub)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    viserrs = M.foldrWithKey
      (\ l (a, b) e -> e *> (collect . pure) (OlappedVis l))
      (pure ())
      (M.intersectionWith (,) locn pubn)

    locm = unPaths loc
    pubm = unPaths pub

-- | A set of assignment and corresponding extraction paths
data DecompBuilder = DecompB
  (Builder Ident Paths)
  (forall a . S.RelPath a => [(a, Patt)])
  
decompPun :: Pun -> DecompBuilder
decompPun (Pun r a) = DecompB (intro r) [(r, a)]
  
instance S.Self DecompBuilder where self_ i = decompPun (S.self_ i)

instance S.Local DecompBuilder where local_ i = decompPun (S.local_ i)

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
    (Builder (P.Vis Ident Ident) VisPaths)
      -- ^ Paths assigned to parts of the pattern
    (forall m a. (S.Path a, S.Extend a, S.Ext a ~ m (), MonadFree (M.Map Ident) m) => Maybe a -> E ([Maybe a], Maybe a))
      -- ^ Value deconstructor

letpath :: Path (P.Vis Ident Ident) -> Patt
letpath p = PattB (introVis p) f
  where
    d = B_ 1 (\ a -> E ([a], Nothing)) []

ungroup :: DecompBuilder -> Patt
ungroup (DecompB g ps) = PattB (fst pfg) (\ a -> liftA2 (,) (snd pgf a) (pext <&> (\ e -> a <&> (#e)))) where
  pgf :: (S.Path a, S.Extend a, S.Ext a ~ m (), MonadFree (M.Map Ident) m) => (Builder (P.Vis Ident Ident) Paths, Maybe a -> E [Maybe a]) 
  pgf = foldMap (\ (Extract f', PattB g f) -> (g, fmap fst f . f')) ps
    
  pext :: MonadFree (M.Map Ident) m => E (m ())
  pext = (disambigmatch . unpaths . build g) (repeat ())

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
  PattB g1 f1 # PattB g2 f2 = PattB (g1 <> g2) f'
    where
      f' a = do
        (vs2, a') <- f2 a
        (vs1, a'') <- f1 a'
        return (vs1++vs2, a'')


newtype Extract = Extract { extract :: forall a . S.Path a => a -> a }

instance S.Self Extract where self_ i = Extract (#. i)

instance S.Field Extract where
  type Compound Extract = Extract
  Extract f #. i = Extract ((#. i) . f)

-- | Build a recursive Block group
data BlockBuilder a = BlockB
  (Builder (P.Vis Ident Ident) VisPaths)
  (E [a])
  
decl :: Path Ident -> BlockBuilder a
decl (PathB f n) = BlockB g []
    where
      g = B_ {size=0, build=VisPaths p p, names=[P.Pub n]}
      
      p :: Paths a
      p = (Paths . M.singleton n . f) (pure Nothing)
    
instance S.Self (BlockBuilder a) where self_ k = decl (S.self_ k)
  
instance S.Field (BlockBuilder a) where
  type Compound (BlockBuilder a) = Path Ident
  b #. k = decl (b S.#. k)

instance S.Let (BlockBuilder a) where
  type Lhs (BlockBuilder a) = Patt
  type Rhs (BlockBuilder a) = E a
  PattB g f #= v = BlockB g (fst <$> f v)
      
instance S.Sep (BlockBuilder a) where
  BlockB g1 v1 #: BlockB g2 v2 = BlockB (g1 <> g2) (v1 <> v2)
  
instance S.Splus (BlockBuilder a) where empty_ = BlockB mempty mempty
    

-- | Tree of paths with one or values contained in leaves and zero or more
--   in internal nodes
--
--   Semigroup and monoid instances defined will union subtrees recursively
--   and accumulate values.
data Amb a = a `Overlap` Maybe (Amb a) | Disjoint (M.Map Ident (Amb a))
  deriving (Functor, Foldable, Traversable)
  
instance Applicative Amb where
  pure a = a `Overlap` Nothing
  (<*>) = ap
  
instance Monad Amb where
  return = pure
  
  a `Overlap` Nothing >>= k = k a
  a `Overlap` Just as >>= k = k a <!> (as >>= k)
  Disjoint ma >>= k = Disjoint ((>>= k) <$> ma)
  
instance MonadFree (M.Map Ident) Amb where
  wrap = Disjoint
  
instance Alt Amb where
  x `Overlap` Just a <!> b = (Overlap x . Just) (a <!> b)
  x `Overlap` Nothing <!> b = x `Overlap` Just b
  a <!> x `Overlap` Nothing = x `Overlap` Just a
  a <!> x `Overlap` Just b = (Overlap x . Just) (a <!> b)
  Disjoint ma <!> Disjoint mb = Disjoint (M.unionWith (<!>) ma mb)

