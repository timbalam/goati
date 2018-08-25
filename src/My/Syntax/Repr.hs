{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Repr
  ( Check, runCheck
  , module My.Syntax.Vocabulary
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr
import qualified My.Types.Syntax.Class as S
import qualified My.Syntax.Import as S (Deps(..))
import My.Syntax.Vocabulary
import My.Util (Collect(..), (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Trans (lift)
import Control.Monad.Free.Church (MonadFree(..), F, iter)
import Data.Bifunctor
import Data.Coerce (coerce)
import Data.List (elemIndex, nub)
import GHC.Exts (IsString(..))
import qualified Data.Map as M
import Bound.Scope (abstractEither, abstract)



type instance S.Member (Repr (Tag k) a) = Repr (Tag k) a

instance S.Tuple (Repr (Tag k) a) where
  type Tup (Repr (Tag k) a) = TupDefns (Check a)
  tup_ (TupDefns m) = 


instance S.Block (Check a) where
  type Rec (Check a) = CheckRec (Rec a)
  block_ b = fmap block_ b
  
{- 
instance (Ord k, Show k, S.Self a, S.Local a) => S.Tuple (Check (Repr (Tag k) a)) where
  type Tup (Check (Repr (Tag k) a)) = TupDefns (Collect [DefnError] (Repr (Tag k) a))
  tup_ b = val . Abs . M.mapKeysMonotonic Key <$> (Check . buildTup) (coerce b)
  
instance (Ord k, Show k) => S.Extend (Check (Repr (Tag k) a)) where
  type Ext (Check (Repr (Tag k) a)) = Check (Repr (Tag k) a)
  (#) = liftA2 update where
    update e w = val (Open e `Update` Open w)
-}  

--type instance S.Member (EBuilder k (P.Vis (Nec Ident) Ident)) =
--  Check (Repr (Tag k) (P.Vis (Nec Ident) Ident))

{-
instance Ord k => S.Deps (BlockDefns (Repr (Tag k) (P.Vis (Nec Ident) Ident))) where
  prelude_ (BlockB g xs) b = b' S.#: b
    where
      -- Build a pattern that introduces a local alias for each
      -- component of the imported prelude Block
      b' :: BlockDefns (Repr (Tag k) (P.Vis (Nec Ident) Ident))
      b' = S.tup_ (foldr puns S.empty_ ns) S.#= S.block_ (BlockB g xs)
      
      puns :: (S.Splus a, S.Local a) => Ident -> a -> a
      puns i a = S.local_ i S.#: a

      -- identifiers for public component names of prelude Block
      ns = nub (map (P.vis id id) (names g))
-}
    
  
-- | Represent whether a free variable can be bound locally
data Bind a b = Parent a | Local b
  deriving Functor

bind :: (a -> c) -> (b -> c) -> Bind a b -> c
bind f _ (Parent a) = f a
bind _ g (Local a) = g a
  
  
-- | Wrapper types and helpers
newtype Group k a = G { getGroup :: Ident -> Repr (Tag k) (Bind Ident a) }
  deriving Functor

instance Ord k => Applicative (Group k) where
  pure = G . const . pure . Local
  (<*>) = ap

instance Ord k => Monad (Group k) where
  return = pure
  G f >>= k = G (\ i -> f i >>= \ a -> case a of
    Parent a -> return (Parent a)
    Local a -> getGroup (k a) i)

--
-- Nested definitions shadow the corresponding 'Super' bound definitions ones on
-- a path basis - e.g. a path declared x.y.z = ... will shadow the .z component of
-- the .y component of the x variable. 
instance (Ord k, Show k) => MonadFree (M.Map Ident) (Group k) where
  wrap m = G (\ i ->
    val ((Open . Var) (Parent i) `Update`
      (Abs . M.mapKeysMonotonic Key)
        (M.mapWithKey (\ i -> abstractSuper . flip getGroup i) m)))
    where
      -- bind parent- scoped public variables to the future 'Super' value
      abstractSuper = abstractEither (bind (Left . Super . Key) (Right . Local))

atvar :: a -> Ident -> Repr (Tag k) a
atvar a k = Comps (Var a) `At` Key k

-- | Build a set of definitions for a 'Tuple' expression
buildTup
  :: (Ord k, Show k)
  => TupDefns (Collect [DefnError] (Repr (Tag k) a))
  -> Collect [DefnError] (M.Map Ident (Scope (Ref (Tag k)) (Repr (Tag k)) a))
buildTup (TupDefns g xs) = liftA2 substexprs (lnode g) (rexprs xs)
  where
    substexprs pubn vs = pubn' where
      pubn' = M.map (f . abstractRef) pubn
      f = (>>= (vs'!!))
      vs' = map lift vs
      
      abstractRef = abstractEither (bind (Left . Super . Key) Right)
  
    -- Right-hand side values to be assigned
    rexprs xs = sequenceA xs
    
    -- Left-hand side paths determine constructed shape
    lnode
      :: (Ord k, Show k) => Defns Ident Paths
      -> Collect [DefnError] (M.Map Ident (Repr (Tag k) (Bind Ident Int)))
    lnode g = M.mapWithKey (flip getGroup) <$> group
      where
        group :: (Ord k, Show k) => Collect [DefnError] (M.Map Ident (Group k Int))
        group = (disambigpub . build g . map pure) [0..]
  
    
-- | Build definitions set for a syntax 'Block' expression
buildBlock
  :: forall k. (Ord k, Show k)
  => BlockDefns (Repr (Tag k) (P.Vis (Nec Ident) Ident))
  -> Collect [DefnError] (M.Map Ident (Scope (Ref (Tag k)) (Repr (Tag k)) (Nec Ident)))
buildBlock (BlockDefns g vs xs) =
  liftA2 substenv (ldefngroups g) (rexprs xs)
  where
    substenv (locn, pubn) vs = pubn' where
      
      -- public variable map, with local-, self- and super-bindings
      pubn' :: M.Map Ident (Scope (Ref (Tag k)) (Repr (Tag k)) (Nec Ident))
      pubn' = M.map (abstractRef . Let (fmap Local <$> locv) . abstractLocal ls . f) pubn
      
      -- bind local- scoped public variables to  the future 'Self' value
      abstractRef o = abstractEither id (o >>= bind
        (return . Left . Super . Key) 
        (P.vis (return . Right) (Left Self `atvar`)))
      
      -- abstract local-bound variables in an expression
      abstractLocal
        :: Monad m
        => [Ident]
        -> m (Bind a (P.Vis (Nec Ident) b))
        -> Scope Int m (Bind a (P.Vis (Nec Ident) b))
      abstractLocal ls = abstract (\ x -> case x of
        Local (P.Priv x) -> maybe Nothing Just (nec (`elemIndex` ls) (`elemIndex` ls) x)
        _                -> Nothing)
      
      -- local variables ordered by bound index
      locv :: Ord k => [Scope Int (Repr (Tag k)) (P.Vis (Nec Ident) Ident)]
      locv = map (\ k -> M.findWithDefault (pure (P.Pub k)) k locn') ls
      
      -- local variable map, with parent-env scoped variables
      locn'
        :: Ord k
        => M.Map Ident (Scope Int (Repr (Tag k)) (P.Vis (Nec Ident) Ident))
      locn' = M.map (freeParent . abstractLocal ls . f) locn 
      
      -- private parent bindable variables are scoped to enclosing env
      freeParent :: Functor f => f (Bind a (P.Vis (Nec a) b)) -> f (P.Vis (Nec a) b)
      freeParent = fmap (bind (P.Priv . Opt) id)
      
      -- insert values by list index
      f :: forall a. Repr (Tag k) (Bind a Int)
        -> Repr (Tag k) (Bind a (P.Vis (Nec Ident) Ident))
      f = (>>= bind (return . Parent) (vs'!!))
      
      -- private free variables are local
      vs' :: forall a. [Repr (Tag k) (Bind a (P.Vis (Nec Ident) Ident))]
      vs' = map (fmap Local) vs
      
      --emptyOpen :: forall k a. (Ord k, Show k) => Repr (Tag k) a
      --emptyOpen = val (Abs M.empty)
      
    
    -- Use the source order for private definition list to make predicting
    -- output expressions easier (alternative would be sorted order)
    ls = nub (map (P.vis id id) (names g))
    
    rexprs = fmap (foldMap id) . liftA2 (zipWith ($)) (traverse extractMatched vs)
    
    ldefngroups
      :: forall k. (Ord k, Show k)
      => Defns (P.Vis Ident Ident) VisPaths
      -> Collect [DefnError] 
        ( M.Map Ident (Repr (Tag k) (Bind Ident Int))
        , M.Map Ident (Repr (Tag k) (Bind Ident Int))
        )
    ldefngroups g = bimap
      (M.mapWithKey (flip getGroup))
      (M.mapWithKey (flip getGroup))
      <$> groups
      where
        groups
          :: (Ord k, Show k)
          => Collect [DefnError] (M.Map Ident (Group k Int), M.Map Ident (Group k Int))
        groups = (disambigvis . build g . map pure) [0..size g]

    
-- | Wrapper to instantiate a path extractor
newtype Extract = Extract { extract :: forall a. S.Path a => a -> a }

instance S.Self Extract where self_ i = Extract (S.#. i)

instance S.Field Extract where
  type Compound Extract = Extract
  Extract f #. i = Extract (\ e -> f e S.#. i)
  

extractMatched
  :: (Ord k, Show k)
  => MatchDefns -> Collect [DefnError] (Repr (Tag k) a -> [Repr (Tag k) a])
extractMatched (MatchDefns g ps) = liftA2 (liftA2 (:)) pext pf
  where
    -- pass extracted value to sub pattern assignments and accumulate
    pf = foldMap id <$> traverse 
      (\ (Extract f, m) -> extractMatched m <&> (. f))
      ps
      
    pext
      :: (Ord k, Show k)
      => Collect [DefnError] (Repr (Tag k) a -> Repr (Tag k) a)
    pext = (fmap maskMatched . disambigmatch . build g . repeat) (pure Nothing)
 

maskMatched
  :: (Ord k, Show k)
  => M.Map Ident (F (M.Map Ident) (Maybe (Repr (Tag k) a -> Repr (Tag k) a)))
  -> Repr (Tag k) a -> Repr (Tag k) a
maskMatched m = maskLayer (M.map (iter (Just . maskLayer)) m) where
  maskLayer
    :: (Ord k, Show k)
    => M.Map Ident (Maybe (Repr (Tag k) a -> Repr (Tag k) a))
    -> Repr (Tag k) a -> Repr (Tag k) a
  maskLayer m e = val (rest `Update` updated) where 
    -- apply mask for the nested layers
    updated = (Abs . M.mapKeysMonotonic Key)
      (M.mapMaybeWithKey (\ k -> fmap (\ f -> (lift . f) (e S.#. k))) m)
    
    rest = hide (M.keys m) (Open e)

    -- | Folds over a value to find keys to restrict for an expression.
    --
    -- Can be used as function to construct an expression of the 'left-over' components
    -- assigned to nested ungroup patterns.
    hide :: Foldable f => f Ident -> Open (Tag k) m a -> Open (Tag k) m a
    hide ks e = foldl (\ e k -> e `Fix` Key k) e ks
