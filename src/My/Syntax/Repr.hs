{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Repr
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


-- | Core representation builder
type instance S.Member (E (Open (Tag k) a)) = E (Open (Tag k) a)

instance Ord k => S.Block (E (Open (Tag k) (P.Vis (Nec Ident) Ident))) where
  type Rec (E (Open (Tag k) (P.Vis (Nec Ident) Ident))) =
    BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) Ident))
  block_ b = Defn . Block . M.map (fmap P.Priv) . M.mapKeysMonotonic Key <$> buildBlock b
  
instance (Ord k, S.Self a, S.Local a) => S.Tuple (E (Open (Tag k) a)) where
  type Tup (E (Open (Tag k) a)) = TupBuilder (E (Open (Tag k) a))
  tup_ b = Defn . Block . M.mapKeysMonotonic Key <$> buildTup b
  
instance S.Extend (E (Open (Tag k) a)) where
  type Ext (E (Open (Tag k) a)) = E (Open (Tag k) a)
  e # w = liftA2 Update e w
  

type instance S.Member (BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) Ident))) =
  E (Open (Tag k) (P.Vis (Nec Ident) Ident))

instance Ord k => S.Deps (BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) Ident))) where
  prelude_ (BlockB g xs) b = b' S.#: b
    where
      -- Build a pattern that introduces a local alias for each
      -- component of the imported prelude Block
      b' :: BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) Ident))
      b' = S.tup_ (foldr puns S.empty_ ns) S.#= S.block_ (BlockB g xs)
      
      puns :: (S.Splus a, S.Local a) => Ident -> a -> a
      puns i a = S.local_ i S.#: a

      -- identifiers for public component names of prelude Block
      ns = names g
    
  
  
-- | Build a set of definitions for a 'Tuple' expression
buildTup
  :: Ord k => TupBuilder (E (Open (Tag k) a))
  -> E (M.Map Ident (Scope Ref (Open (Tag k)) a))
buildTup (TupB g xs) = liftA2 substexprs (lnode g) (rexprs xs)
  where
    substexprs pubn vs = pubn' where
      pubn' = M.map (f . abstractRef) pubn
      f = (>>= (vs'!!))
      vs' = map lift vs
      
      abstractRef o = abstractEither id (o >>= bind (Left Super `atvar`) (return . Right))
  
    -- Right-hand side values to be assigned
    rexprs :: [E a] -> E [a]
    rexprs xs = sequenceA xs
    
    -- Left-hand side paths determine constructed shape
    lnode:: Ord k => Builder Paths -> E (M.Map Ident (Open (Tag k) (Bind Ident Int)))
    lnode g = (coerce . unPaths) (build g [0..])
  
  
-- | Represent whether a free variable can be bound locally
data Bind a b = Parent a | Local b

bind :: (a -> c) -> (b -> c) -> Bind a b -> c
bind f _ (Parent a) = f a
bind _ g (Local a) = g a
  
  
newtype TupExpr k a = TupE { getTupExpr :: Open (Tag k) (Bind Ident a) }
  deriving Functor

instance Ord k => Applicative (TupExpr k)
  pure = TupE . pure . Local
  (<*>) = ap

instance Ord k => Monad (TupExpr k) where
  return = pure
  TupE o >>= f = TupE (o >>= \ a -> case a of
    Parent a -> return (Parent a)
    Local a -> getTupExpr (f a))
    
instance Ord k => MonadFree (M.Map Ident) (TupExpr k) where
  wrap = TupE . Update (Var (Parent k)) . Defn . Block . M.mapKeysMonotonic Key
    . M.map (abstractSuper . getTupExpr)
    where
      -- bind parent- scoped public variables to the future 'Super' value
      abstractSuper o = abstractEither id (o >>= \ a -> case a of
        Parent k -> Left Super `atvar` k
        Local b -> (return . Right) (Local b))
        
        
atvar :: a -> Ident -> Open (Tag k) a
atvar a k = selfApp (Var a) `At` Key k
  
    
-- | Build definitions set for a syntax 'Block' expression
buildBlock
  :: forall k . Ord k
  => BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) Ident))
  -> E (M.Map Ident (Scope Ref (Open (Tag k)) (Nec Ident)))
buildBlock (BlockB g xs) = liftA2 substenv (ldefngroups g) (rexprs xs)
  where
    substenv (locn, pubn) vs = pubn' where
      
      -- public variable map, with local-, self- and super-bindings
      pubn' :: M.Map Ident (Scope Ref (Open (Tag k)) (Nec Ident))
      pubn' = M.map (abstractRef . Let (fmap Local <$> locv) . abstractLocal ls . f) pubn
      
      -- bind local- scoped public variables to  the future 'Self' value
      abstractRef o = abstractEither id (o >>= bind
        (Left Super `atvar`) 
        (P.vis (return . Right) (Left Self `atvar`)))
      
      -- abstract local-bound variables in an expression
      abstractLocal ls = abstract (\ x -> case x of
        Local (P.Priv x) -> maybe Nothing Just (nec (`elemIndex` ls) (`elemIndex` ls) x)
        _                -> Nothing)
      
      -- local variables ordered by bound index
      locv :: Ord k => [Scope Int (Open (Tag k)) (P.Vis (Nec Ident) Ident)]
      locv = map (\ k -> M.findWithDefault (pure (P.Pub k)) k locn') ls
      
      -- local variable map, with parent-env scoped variables
      locn'
        :: Ord k
        => M.Map Ident (Scope Int (Open (Tag k)) (P.Vis (Nec Ident) Ident))
      locn' = M.map (freeParent . abstractLocal ls . f) locn 
      
      -- private parent bindable variables are scoped to enclosing env
      freeParent = fmap (bind (P.Priv . Opt) id)
      
      -- insert values by list index
      f :: forall a. Open (Tag k) (Bind a Int)
        -> Open (Tag k) (Bind  a (P.Vis (Nec Ident) Ident))
      f = (>>= bind (return . Parent) (vs'!!))
      
      -- private free variables are local
      vs' :: forall a. [Open (Tag k) (Bind a (P.Vis (Nec Ident) Ident))]
      vs' = map (fmap Local) vs
      
    
    -- Use the source order for private definition list to make predicting
    -- output expressions easier (alternative would be sorted order)
    ls = nub (names g)
    
    rexprs :: forall a . E [a] -> E [a]
    rexprs = id 
    
    ldefngroups
      :: forall k . Ord k
      => Builder VisPaths
      -> E 
        ( M.Map Ident (Open (Tag k) (Bind Ident Int))
        , M.Map Ident (Open (Tag k) (Bind Ident Int))
        )
    ldefngroups g = (E . validatevis . build g) [0..size g]
    
    
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

    
-- | A 'Pattern' is a value deconstructor and a group of paths to assign
data PattBuilder =
  PattB
    (Builder VisPaths)
    (forall k a . Ord k => E (Open (Tag k) a -> [Open (Tag k) a]))

-- | An ungroup pattern
data Ungroup =
  Ungroup
    PattBuilder
    -- ^ Builds the set of local and public assignments made by rhs patterns, where
    -- assigned values are obtained by deconstructing an original value
    [Ident]
    -- ^ List of fields of the original value used to obtain deconstructed values    
    
letpath :: P.Vis Path Path -> PattBuilder
letpath p = PattB (introVis p) (pure pure)

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
    
ungroup :: TupBuilder PattBuilder -> Ungroup
ungroup (TupB g ps) =
  Ungroup (PattB pg pf) (names g)
  where
    pf :: Ord k => E (Open (Tag k) a -> [Open (Tag k) a])
    pf = liftA2 applydecomp (ldecomp g) (snd pgfs)
  
    ldecomp :: Ord k => Builder Paths -> E (Open (Tag k) a -> [Open (Tag k) a])
    ldecomp g = (validatedecomp . unPaths . build g . repeat) (pure pure)
  
    applydecomp :: Monoid b => (a -> [a]) -> [a -> b] -> (a -> b)
    applydecomp s fs a = fold (zipWith ($) fs (s a))
    
    --pg :: Builder VisPaths
    pg = fst (pgfs :: (Builder VisPaths, E [Open (Tag ()) a -> [Open (Tag ()) a]]))
    pgfs :: Ord k => (Builder VisPaths, E [Open (Tag k) a -> [Open (Tag k) a]])
    pgfs = foldMap (\ (PattB g f) -> (g, pure <$> f)) ps
    
instance Semigroup PattBuilder where
  PattB g1 v1 <> PattB g2 v2 = PattB (g1 <> g2) (v1 <> v2)
  
instance Monoid PattBuilder where
  mempty = PattB mempty mempty
  mappend = (<>)
  
instance S.Self PattBuilder where self_ i = letpath (S.self_ i)
  
instance S.Local PattBuilder where local_ i = letpath (S.local_ i)
  
instance S.Field PattBuilder where
  type Compound PattBuilder = P.Vis Path Path
  v #. k = letpath (v S.#. k)

type instance S.Member PattBuilder = PattBuilder
type instance S.Member Ungroup = PattBuilder

instance S.Tuple PattBuilder where
  type Tup PattBuilder = TupBuilder PattBuilder
  tup_ g = p where Ungroup p _ = ungroup g
  
instance S.Tuple Ungroup where
  type Tup Ungroup = TupBuilder PattBuilder
  tup_ = ungroup
  
instance S.Extend PattBuilder where
  type Ext PattBuilder = Ungroup
  (#) = letungroup
    
-- | Build a recursive Block group
data BlockBuilder a = BlockB (Builder VisPaths) (E [a])

instance Semigroup (BlockBuilder a) where
  BlockB g1 v1 <> BlockB g2 v2 = BlockB (g1 <> g2) (v1 <> v2)
  
instance Monoid (BlockBuilder a) where
  mempty = BlockB mempty mempty
  mappend = (<>)
  
decl :: Path -> BlockBuilder a
decl (PathB f n) = BlockB g (pure [])
    where
      g = B_ {size=0, build=const (VisPaths p p), names=[n]}
      
      p :: forall a . Paths a
      p = Paths ((M.singleton n . f) (pure Nothing))
    
instance S.Self (BlockBuilder a) where
  self_ k = decl (S.self_ k)
  
instance S.Field (BlockBuilder a) where
  type Compound (BlockBuilder a) = Path
  b #. k = decl (b S.#. k)

instance Ord k => S.Let (BlockBuilder (Open (Tag k) a)) where
  type Lhs (BlockBuilder (Open (Tag k) a)) = PattBuilder
  type Rhs (BlockBuilder (Open (Tag k) a)) = E (Open (Tag k) a)
  PattB g f #= v = BlockB g (f <*> v)
      
instance S.Sep (BlockBuilder a) where
  BlockB g1 v1 #: BlockB g2 v2 = BlockB (g1 <> g2) (v1 <> v2)
  
instance S.Splus (BlockBuilder a) where
  empty_ = BlockB mempty mempty
    
    
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
data An a = An a (Maybe (An a)) | Un (M.Map Ident (An a))
  deriving (Functor, Foldable, Traversable)
  
instance Applicative An where
  pure a = An a Nothing
  (<*>) = ap
  
instance Monad An where
  return = pure
  
  An a Nothing >>= k = k a
  An a (Just as) >>= k = k a <!> (as >>= k)
  Un ma >>= k = Un ((>>= k) <$> ma)
  
instance MonadFree (M.Map Ident) An where
  wrap = Un
  
instance Alt An where
  An x (Just a) <!> b = (An x . Just) (a <!> b)
  An x Nothing <!> b = An x (Just b)
  a <!> An x Nothing = An x (Just a)
  a <!> An x (Just b) = (An x . Just) (a <!> b)
  Un ma <!> Un mb = Un (M.unionWith (<!>) ma mb)

