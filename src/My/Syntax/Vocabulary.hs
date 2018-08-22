{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | This module contains functions for abstractly validating sets of definitions made
-- using the syntax classes for duplicated names, overlapping definitions, etc. 
module My.Syntax.Vocabulary
  ( DefnError(..)
  , Defns(..), Paths(..), VisPaths(..)
  , disambigpub, disambigpriv, disambigvis, disambigmatch
  , Path(..), PattDefns(..), Pun(..)
  , BlockDefns(..), TupDefns(..), MatchDefns(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr (Ident)
import My.Types.Classes (MyError(..))
import qualified My.Types.Syntax.Class as S
import My.Util (Collect(..), collect, (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free (MonadFree(..))
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
  
  
-- | Abstractly represents a group of definitions. The monoid instance merges 
-- groups of definitions. 
data Defns k tree = Defns
  { size :: Int
    -- ^ number of values to assign / paths
  , build :: forall a . [a] -> tree a
    -- ^ builder function that performs assignment
  , names :: [k]
    -- ^ list of top-level names in assignment order
  }
  
instance Alt tree => Semigroup (Defns k tree) where
  Defns sz1 b1 n1 <> Defns sz2 b2 n2 =
    Defns (sz1 + sz2) b (n1 <> n2)
    where
      b :: forall a . [a] -> tree a
      b xs = let (x1, x2) = splitAt sz1 xs in b1 x1 <!> b2 x2
  
instance Plus tree => Monoid (Defns k tree) where
  mempty = Defns 0 (const zero) mempty
  mappend = (<>)
  
hoistDefns :: (forall x . f x -> g x) -> Defns i f -> Defns i g
hoistDefns f (Defns sz b n) = Defns sz (f . b) n

    
-- | A 'Path' is a sequence of nested names. We represent as an insert function for
-- nested paths.
data Path k = Path
    (forall a. Amb a -> (Ident, Amb a))
    -- ^ push additional fields onto path
    k
    -- ^ top-level field name

instance S.Self k => S.Self (Path k) where self_ i = Path (i,) (S.self_ i)
instance S.Local k => S.Local (Path k) where local_ i = Path (i,) (S.local_ i)
  
instance S.Field (Path k) where
  type Compound (Path k) = Path k
  Path f k #. i = Path (f . wrap . M.singleton i) k
    
    
-- | A set of paths possibly with associated values of type 'a'.
newtype Paths a = Paths { unPaths :: M.Map Ident (Amb (Maybe a)) }
  deriving Functor
  
instance Alt Paths where Paths m1 <!> Paths m2 = Paths (M.unionWith (<!>) m1 m2)
instance Plus Paths where zero = Paths M.empty

-- | 'intro' forms a singleton path group
intro :: Path k -> Defns k Paths
intro (Path f k) =
  Defns 1 (Paths . uncurry M.singleton . f . pure . Just . head) [k]
  
instance S.Self k => S.Self (Defns k Paths) where self_ i = intro (S.self_ i)
instance S.Local k => S.Local (Defns k Paths) where local_ i = intro (S.local_ i)
  
instance S.Field (Defns k Paths) where
  type Compound (Defns k Paths) = Path k
  p #. k = intro (p S.#. k)

-- | Validate that a finished tree has unambiguous paths and construct 
-- an expression that reflects the tree of assigned values.
--
-- If there are any ambiguous paths, returns them as list of 'OlappedSet'
-- errors.
--
-- Paths with missing 'Nothing' values represent paths that are validated but
-- not assigned, and unassigned trees of paths are not included in output.
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
        
        
-- | Paths partitioned by top-level visibility
data VisPaths a = VisPaths { local :: Paths a, public :: Paths a }
  deriving Functor

instance Alt VisPaths where
  VisPaths l1 s1 <!> VisPaths l2 s2 = VisPaths (l1 <!> l2) (s1 <!> s2)

instance Plus VisPaths where zero = VisPaths zero zero
    
introVis :: Path (P.Vis Ident Ident) -> Defns (P.Vis Ident Ident) VisPaths
introVis p@(Path _ (P.Priv _)) = hoistDefns (\ b -> zero {local = b}) (intro p) 
introVis p@(Path _ (P.Pub _)) = hoistDefns (\ b -> zero {public = b}) (intro p)

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
        

-- | Validate that a group of matched paths are disjoint
disambigmatch
  :: MonadFree (M.Map Ident) m
  => Paths (Collect [DefnError] a)
  -> Collect [DefnError] (M.Map Ident (m a))
disambigmatch = disambig (OlappedMatch . fmap P.K_)
        

-- | A 'Tuple' definition associates a group of paths with values.
data TupDefns a = TupDefns (Defns Ident Paths) [a] -- ^ values in assignment order

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun b = Pun (forall a. S.RelPath a => a) b

pun :: Pun a -> TupDefns a
pun (Pun p a) = TupDefns p [a]

instance S.Self a => S.Self (Pun a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance S.Local a => S.Local (Pun a) where local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field a => S.Field (Pun a) where
  type Compound (Pun a) = Pun (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

instance S.Self a => S.Self (TupDefns a) where self_ i = pun (S.self_ i)
instance S.Local a => S.Local (TupDefns a) where local_ i = pun (S.local_ i)

instance S.Field a => S.Field (TupDefns a) where
  type Compound (TupDefns a) = Pun (S.Compound a)
  pb #. k = pun (pb S.#. k)

instance S.Let (TupDefns a) where
  type Lhs (TupDefns a) = Defns Ident Paths
  type Rhs (TupDefns a) = a
  b #= a = TupDefns b [a]

instance S.Sep (TupDefns a) where
  TupDefns g1 a1 #: TupDefns g2 a2 = TupDefns (g1 <> g2) (a1 <> a2)
  
instance S.Splus (TupDefns a) where empty_ = TupDefns mempty mempty


-- | A pattern definition represents the simultaneous decomposing a value into distinct
-- parts and the assignment of the parts
data PattDefns = PattDefns
  (Defns (P.Vis Ident Ident) VisPaths)
  -- ^ Assign matched and unmatched paths
  MatchDefns


data MatchDefns = MatchDefns
  (Defns Ident Paths)
  -- ^ Paths to extract
  (forall a . S.RelPath a => [(a, MatchDefns)])
  -- ^ Nested patterns for extracted paths
  
instance Semigroup MatchDefns where
  MatchDefns g1 v1 <> MatchDefns g2 v2 = MatchDefns (g1 <> g2) (v1 <> v2)
  
instance Monoid MatchDefns where
  mempty = MatchDefns mempty mempty
  mappend = (<>)
  
-- | A tuple decomposing pattern
data DecompDefns = DecompDefns
  (Defns (P.Vis Ident Ident) VisPaths)
  -- ^ Paths assigned by rhs patterns
  MatchDefns

-- | Match the implicit left-over value
letpath :: Path (P.Vis Ident Ident) -> PattDefns
letpath p = PattDefns (introVis p) mempty

-- | Ignore the implicit left-over value
nopath :: Plus g => Defns k g
nopath = Defns {size=1,build=const zero,names=[]}

matchPun :: Pun PattDefns -> DecompDefns
matchPun (Pun r (PattDefns g a)) = DecompDefns g (MatchDefns r [(r,a)])
  
instance S.Self DecompDefns where self_ i = matchPun (S.self_ i)
instance S.Local DecompDefns where local_ i = matchPun (S.local_ i)

instance S.Field DecompDefns where
  type Compound DecompDefns = Pun (Path (P.Vis Ident Ident))
  p #. k = matchPun (p S.#. k)

instance S.Let DecompDefns where
  type Lhs DecompDefns = Pun PattDefns
  type Rhs DecompDefns = PattDefns
  Pun r _ #= PattDefns g v = DecompDefns g (MatchDefns r [(r, v)])

instance S.Sep DecompDefns where
  DecompDefns g1 v1 #: DecompDefns g2 v2 = DecompDefns (g1 <> g2) (v1 <> v2)

instance S.Splus DecompDefns where
  empty_ = DecompDefns mempty mempty
 
 
instance S.Self PattDefns where self_ i = letpath (S.self_ i)
instance S.Local PattDefns where local_ i = letpath (S.local_ i)
  
instance S.Field PattDefns where
  type Compound PattDefns = Path (P.Vis Ident Ident)
  v #. k = letpath (v S.#. k)

type instance S.Member PattDefns = PattDefns

instance S.Tuple PattDefns where
  type Tup PattDefns = DecompDefns
  tup_ (DecompDefns g v) = PattDefns (nopath <> g) v where
  
instance S.Extend PattDefns where
  type Ext PattDefns = DecompDefns
  PattDefns g1 v1 # DecompDefns g2 v2 =
    PattDefns (g1 <> g2) (v1 <> v2)


-- | A block associates a set of patterns with values
data BlockDefns a = BlockDefns
  (Defns (P.Vis Ident Ident) VisPaths)
  [MatchDefns]
  (Collect [DefnError] [a])
  
decl :: Path Ident -> BlockDefns a
decl (Path f n) = BlockDefns g [] (pure [])
    where
      g = Defns {size=0, build=const (VisPaths p p), names=[P.Pub n]}
      
      p :: Paths a
      p = (Paths . uncurry M.singleton . f) (pure Nothing)
    
instance S.Self (BlockDefns a) where self_ k = decl (S.self_ k)
  
instance S.Field (BlockDefns a) where
  type Compound (BlockDefns a) = Path Ident
  b #. k = decl (b S.#. k)

instance S.Let (BlockDefns a) where
  type Lhs (BlockDefns a) = PattDefns
  type Rhs (BlockDefns a) = Collect [DefnError] a
  PattDefns g m #= v = BlockDefns g [m] (pure <$> v)
      
instance S.Sep (BlockDefns a) where
  BlockDefns g1 m1 v1 #: BlockDefns g2 m2 v2 =
    BlockDefns (g1 <> g2) (m1 <> m2) (liftA2 (<>) v1 v2)
  
instance S.Splus (BlockDefns a) where empty_ = BlockDefns mempty mempty (pure mempty)
    

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
  Disjoint ma >>= k = Disjoint ((>>= k) <$> ma)
  
instance MonadFree (M.Map Ident) Amb where
  wrap = Disjoint
  
instance Alt Amb where
  x `Overlap` Just a <!> b = (Overlap x . Just) (a <!> b)
  x `Overlap` Nothing <!> b = x `Overlap` Just b
  a <!> x `Overlap` Nothing = x `Overlap` Just a
  a <!> x `Overlap` Just b = (Overlap x . Just) (a <!> b)
  Disjoint ma <!> Disjoint mb = Disjoint (M.unionWith (<!>) ma mb)

