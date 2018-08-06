{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Validate syntactic block name hierarchies
module My.Syntax.Vocabulary
  ( DefnError(..)
  , Builder(..), Paths(..), VisPaths(..)
  , disambigpub, disambigpriv, disambigvis
  , Path(..), Patt(..), Pun(..)
  , BlockBuilder(..), TupBuilder(..), DecompBuilder(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr (Ident)
import My.Types.Classes (MyError(..))
import qualified My.Types.Syntax.Class as S
import My.Util (Collect(..), collect, (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free.Church (MonadFree(..), F, iter)
import Data.Semigroup
import Data.Functor.Plus (Plus(..), Alt(..))
import Data.Typeable
import qualified Data.Map as M
--import qualified Data.Set as S
import GHC.Exts (IsString(..))


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
  
hoistBuilder :: (forall x . f x -> g x) -> Builder i f -> Builder i g
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
  p #. k = intro (p S.#. k)

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
  :: MonadFree (M.Map Ident) m
  => Paths (Collect [DefnError] a) -> Collect [DefnError] (M.Map Ident (m a))
disambigpub = disambig (OlappedSet . P.Pub . fmap P.K_)
disambigpriv = disambig (OlappedSet . P.Priv)

disambig
  :: MonadFree (M.Map Ident) m
  => (P.Path Ident -> DefnError)
  -> Paths (Collect [DefnError] a) -> Collect [DefnError] (M.Map Ident (m a))
disambig f (Paths m) = M.traverseMaybeWithKey (go . P.Pure) m
  where
    go _ (Overlap mb Nothing) = fmap pure <$> sequenceA mb
    go p (Overlap _ (Just b)) = (collect . pure) (f p) *> go p b
    go p (Disjoint m) = Just . wrap
        <$> M.traverseMaybeWithKey (go . P.Free . P.At p . P.K_) m

-- | A punned assignment statement
data Pun b = Pun (forall a. S.RelPath a => a) b

instance S.Self a => S.Self (Pun a) where
  self_ i = Pun (S.self_ i) (S.self_ i)

instance S.Local a => S.Local (Pun a) where
  local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field a => S.Field (Pun a) where
  type Compound (Pun a) = Pun (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

-- | A 'Tuple' is a group of paths with associated values
data TupBuilder a = TupB (Builder Ident Paths) [a] -- ^ values in assignment order

pun :: Pun a -> TupBuilder a
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

-- | Paths partitioned by top-level visibility
data VisPaths a = VisPaths { local :: Paths a, public :: Paths a }
  deriving Functor

instance Alt VisPaths where
  VisPaths l1 s1 <!> VisPaths l2 s2 = VisPaths (l1 <!> l2) (s1 <!> s2)

instance Plus VisPaths where
  zero = VisPaths zero zero
    
introVis :: Path (P.Vis Ident Ident) -> Builder (P.Vis Ident Ident) VisPaths
introVis p@(PathB _ (P.Priv _)) = hoistBuilder (\ b -> zero {local = b}) (intro p) 
introVis p@(PathB _ (P.Pub _)) = hoistBuilder (\ b -> zero {public = b}) (intro p)

-- | Validate that a group of private/public definitions are disjoint.
disambigvis
  :: MonadFree (M.Map Ident) m
  => VisPaths (Collect [DefnError] a)
  -> Collect [DefnError] (M.Map Ident (m a), M.Map Ident (m a))
disambigvis (VisPaths {local=loc, public=pub}) =
  viserrs *> liftA2 (,) (disambigpriv loc) (disambigpub pub)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    viserrs = M.foldrWithKey
      (\ l (a, b) e -> e *> (collect . pure) (OlappedVis l))
      (pure ())
      (M.intersectionWith (,) locn pubn)

    locn = unPaths loc
    pubn = unPaths pub

-- | A set of assignment and corresponding extraction paths
data DecompBuilder = DecompB
  (Builder Ident Paths)
  (forall a . S.RelPath a => [(a, Patt)])
  
decompPun :: Pun Patt -> DecompBuilder
decompPun (Pun r a) = DecompB r [(r, a)]
  
instance S.Self DecompBuilder where self_ i = decompPun (S.self_ i)

instance S.Local DecompBuilder where local_ i = decompPun (S.local_ i)

instance S.Field DecompBuilder where
  type Compound DecompBuilder = Pun (Path (P.Vis Ident Ident))
  p #. k = decompPun (p S.#. k)

instance S.Let DecompBuilder where
  type Lhs DecompBuilder = Pun Patt
  type Rhs DecompBuilder = Patt
  Pun r _ #= p = DecompB r [(r, p)]

instance S.Sep DecompBuilder where
  DecompB g1 v1 #: DecompB g2 v2 = DecompB (g1 <> g2) (v1 <> v2)

instance S.Splus DecompBuilder where
  empty_ = DecompB mempty mempty
  


-- | A pattern represents decomposing a value and assignment of distinct parts
data Patt =
  PattB
    (Builder (P.Vis Ident Ident) VisPaths)
      -- ^ Paths assigned to parts of the pattern
    (forall a. (S.Path a, S.Extend a, S.Ext a ~ M.Map Ident (Maybe (a -> a)))
      => Collect [DefnError] (Maybe a -> ([Maybe a], Maybe a)))
      -- ^ Value deconstructor

letpath :: Path (P.Vis Ident Ident) -> Patt
letpath p = PattB (introVis p) d
  where
    d :: Applicative f => f (Maybe a -> ([Maybe a], Maybe a))
    d = pure (\ a -> ([a], Nothing))
    
newtype D = D (forall a . (S.Path a, S.Extend a, S.Ext a ~ M.Map Ident (Maybe (a -> a)))
  => Collect [DefnError] (Maybe a -> [Maybe a]))
  
instance Monoid D where
  mempty = D (pure mempty)
  D a `mappend` D b = D (liftA2 mappend a b)

ungroup :: DecompBuilder -> Patt
ungroup (DecompB g ps) = PattB
  pg
  (liftA2 (<<*>>) pf (fmap <$> pext))
  where
    (<<*>>) :: (a -> b) -> (a -> c) -> a -> (b, c)
    (<<*>>) f g a = (f a, g a)
  
    (pg, D pf) = foldMap
      (\ (Extract f', PattB g f) -> (g, D ((fst .) <$> (. fmap f') <$> f)))
      ps
      
    pext
      :: (S.Path a, S.Extend a, S.Ext a ~ M.Map Ident (Maybe (a -> a)))
      => Collect [DefnError] (a -> a)
    pext = (fmap maskmatch . disambigmatch . build g . repeat) (pure Nothing)
 

disambigmatch
  :: MonadFree (M.Map Ident) m
  => Paths (Collect [DefnError] a)
  -> Collect [DefnError] (M.Map Ident (m a))
disambigmatch = disambig (OlappedMatch . fmap P.K_)

maskmatch
  :: (S.Path a, S.Extend a, S.Ext a ~ M.Map Ident (Maybe (a -> a)))
  => M.Map Ident (F (M.Map Ident) (Maybe (a -> a))) -> a -> a
maskmatch m = f (iter (Just . f) <$> m) where
  f m = (S.# M.mapWithKey (\ k -> fmap (. (S.#. k))) m)
  
instance S.Self Patt where self_ i = letpath (S.self_ i)
  
instance S.Local Patt where local_ i = letpath (S.local_ i)
  
instance S.Field Patt where
  type Compound Patt = Path (P.Vis Ident Ident)
  v #. k = letpath (v S.#. k)

type instance S.Member Patt = Patt

instance S.Tuple Patt where
  type Tup Patt = DecompBuilder
  tup_ g = ungroup g
  
instance S.Extend Patt where
  type Ext Patt = Patt
  PattB g1 f1 # PattB g2 f2 = PattB (g1 <> g2) (liftA2 seqf f1 f2)
    where
      seqf f1 f2 a = (vs1++vs2, a'') where
        (vs2, a') = f2 a
        (vs1, a'') = f1 a'


newtype Extract = Extract { extract :: forall a . S.Path a => a -> a }

instance S.Self Extract where self_ i = Extract (S.#. i)

instance S.Field Extract where
  type Compound Extract = Extract
  Extract f #. i = Extract ((S.#. i) . f)

-- | Build a recursive Block group
data BlockBuilder a = BlockB
  (Builder (P.Vis Ident Ident) VisPaths)
  (Collect [DefnError] [Maybe a])
  
decl :: Path Ident -> BlockBuilder a
decl (PathB f n) = BlockB g (pure [])
    where
      g = B_ {size=0, build=const (VisPaths p p), names=[P.Pub n]}
      
      p :: Paths a
      p = (Paths . uncurry M.singleton . f) (pure Nothing)
    
instance S.Self (BlockBuilder a) where self_ k = decl (S.self_ k)
  
instance S.Field (BlockBuilder a) where
  type Compound (BlockBuilder a) = Path Ident
  b #. k = decl (b S.#. k)

instance (S.Path a, S.Extend a, S.Ext a ~ M.Map Ident (Maybe (a -> a)))
  => S.Let (BlockBuilder a) where
  type Lhs (BlockBuilder a) = Patt
  type Rhs (BlockBuilder a) = Collect [DefnError] a
  PattB g f #= v = (BlockB g . fmap fst . (f <*>)) (Just <$> v)
      
instance S.Sep (BlockBuilder a) where
  BlockB g1 v1 #: BlockB g2 v2 = BlockB (g1 <> g2) (liftA2 (<>) v1 v2)
  
instance S.Splus (BlockBuilder a) where empty_ = BlockB mempty (pure mempty)
    

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

