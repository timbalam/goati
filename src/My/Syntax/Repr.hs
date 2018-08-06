{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Repr
  ( E, runE, EBuilder(..)
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
import Control.Monad.Free (MonadFree(..))
import Data.Bifunctor
import Data.Coerce (coerce)
import Data.List (elemIndex, nub)
import GHC.Exts (IsString(..))
import qualified Data.Map as M
import Bound.Scope (abstractEither, abstract)


-- | Wrapper for applicative syntax error checking
newtype E a = E (Collect [DefnError] a)
  deriving (Functor, Applicative)
  
runE :: E a -> Either [DefnError] a
runE (E e) = getCollect e
  
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
  
-- | Core representation builder
newtype EBuilder k a = EB { getEBuilder :: BlockBuilder (Ungroup k a) }
  deriving (S.Self, S.Sep, S.Splus)
  
instance S.Field (EBuilder k a) where
  type Compound (EBuilder k a) = Path Ident
  p #. i = EB (p S.#. i)
  
instance Ord k => S.Let (EBuilder k a) where
  type Lhs (EBuilder k a) = Patt
  type Rhs (EBuilder k a) = E (Open (Tag k) a)
  l #= r = EB (l S.#= coerce r)

type instance S.Member (E (Open (Tag k) a)) = E (Open (Tag k) a)

instance Ord k => S.Block (E (Open (Tag k) (P.Vis (Nec Ident) Ident))) where
  type Rec (E (Open (Tag k) (P.Vis (Nec Ident) Ident))) = EBuilder k (P.Vis (Nec Ident) Ident)
  block_ (EB b) = Defn . Block . M.map (fmap P.Priv) . M.mapKeysMonotonic Key
    <$> (E . buildBlock) (coerce b)
  
instance (Ord k, S.Self a, S.Local a) => S.Tuple (E (Open (Tag k) a)) where
  type Tup (E (Open (Tag k) a)) = TupBuilder (E (Open (Tag k) a))
  tup_ b = Defn . Block . M.mapKeysMonotonic Key <$> (E . buildTup) (coerce b)
  
instance S.Extend (E (Open (Tag k) a)) where
  type Ext (E (Open (Tag k) a)) = E (Open (Tag k) a)
  e # w = liftA2 Update e w
  

--type instance S.Member (EBuilder k (P.Vis (Nec Ident) Ident)) =
--  E (Open (Tag k) (P.Vis (Nec Ident) Ident))

{-
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
      ns = nub (map (P.vis id id) (names g))
-}
    
  
-- | Represent whether a free variable can be bound locally
data Bind a b = Parent a | Local b
  deriving Functor

bind :: (a -> c) -> (b -> c) -> Bind a b -> c
bind f _ (Parent a) = f a
bind _ g (Local a) = g a
  
  
-- | Wrapper types and helpers
newtype Group k a = G { getGroup :: Ident -> Open (Tag k) (Bind Ident a) }
  deriving Functor

instance Ord k => Applicative (Group k) where
  pure = G . const . pure . Local
  (<*>) = ap

instance Ord k => Monad (Group k) where
  return = pure
  G f >>= k = G (\ i -> f i >>= \ a -> case a of
    Parent a -> return (Parent a)
    Local a -> getGroup (k a) i)

instance Ord k => MonadFree (M.Map Ident) (Group k) where
  wrap m = G (\ i ->
    Var (Parent i) `Update`
      (Defn . Block . M.mapKeysMonotonic Key)
        (M.mapWithKey (\ i -> abstractSuper . flip getGroup i) m))
    where
      -- bind parent- scoped public variables to the future 'Super' value
      abstractSuper o = abstractEither id (o >>= \ a -> case a of
        Parent k -> Left Super `atvar` k
        Local b -> (return . Right) (Local b))

atvar :: a -> Ident -> Open (Tag k) a
atvar a k = selfApp (Var a) `At` Key k

-- | Build a set of definitions for a 'Tuple' expression
buildTup
  :: Ord k
  => TupBuilder (Collect [DefnError] (Open (Tag k) a))
  -> Collect [DefnError] (M.Map Ident (Scope Ref (Open (Tag k)) a))
buildTup (TupB g xs) = liftA2 substexprs (lnode g) (rexprs xs)
  where
    substexprs pubn vs = pubn' where
      pubn' = M.map (f . abstractRef) pubn
      f = (>>= (vs'!!))
      vs' = map lift vs
      
      abstractRef o = abstractEither id (o >>= bind (Left Super `atvar`) (return . Right))
  
    -- Right-hand side values to be assigned
    rexprs xs = sequenceA xs
    
    -- Left-hand side paths determine constructed shape
    lnode
      :: Ord k => Builder Ident Paths
      -> Collect [DefnError] (M.Map Ident (Open (Tag k) (Bind Ident Int)))
    lnode g = M.mapWithKey (flip getGroup) <$> group
      where
        group :: Ord k => Collect [DefnError] (M.Map Ident (Group k Int))
        group = (disambigpub . build g . map pure) [0..]
  
    
-- | Build definitions set for a syntax 'Block' expression
buildBlock
  :: forall k . Ord k
  => BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) Ident))
  -> Collect [DefnError] (M.Map Ident (Scope Ref (Open (Tag k)) (Nec Ident)))
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
      abstractLocal
        :: Monad m
        => [Ident]
        -> m (Bind a (P.Vis (Nec Ident) b))
        -> Scope Int m (Bind a (P.Vis (Nec Ident) b))
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
      freeParent :: Functor f => f (Bind a (P.Vis (Nec a) b)) -> f (P.Vis (Nec a) b)
      freeParent = fmap (bind (P.Priv . Opt) id)
      
      -- insert values by list index
      f :: forall a. Open (Tag k) (Bind a Int)
        -> Open (Tag k) (Bind a (P.Vis (Nec Ident) Ident))
      f = (>>= bind (return . Parent) (vs'!!))
      
      -- private free variables are local
      vs' :: forall a. [Open (Tag k) (Bind a (P.Vis (Nec Ident) Ident))]
      vs' = map (maybe emptyOpen (fmap Local)) vs
      
      emptyOpen :: forall k a. Open k a
      emptyOpen = Defn (Block M.empty)
      
    
    -- Use the source order for private definition list to make predicting
    -- output expressions easier (alternative would be sorted order)
    ls = nub (map (P.vis id id) (names g))
    
    rexprs = id
    
    ldefngroups
      :: forall k . Ord k
      => Builder (P.Vis Ident Ident) VisPaths
      -> Collect [DefnError] 
        ( M.Map Ident (Open (Tag k) (Bind Ident Int))
        , M.Map Ident (Open (Tag k) (Bind Ident Int))
        )
    ldefngroups g = bimap
      (M.mapWithKey (flip getGroup))
      (M.mapWithKey (flip getGroup))
      <$> groups
      where
        groups
          :: Collect [DefnError] (M.Map Ident (Group k Int), M.Map Ident (Group k Int))
        groups = (disambigvis . build g . map pure) [0..size g]
    

    
-- | A deconstructed value assigned in a left-over pattern
newtype Ungroup k a = Ungroup { getUngroup :: Open (Tag k) a }
  deriving (Functor, Applicative, Monad, S.Self, S.Local)
  
instance S.Field (Ungroup k a) where
  type Compound (Ungroup k a) = Ungroup k a
  Ungroup o #. k = Ungroup (o S.#. k)

instance Ord k => S.Extend (Ungroup k a) where
  type Ext (Ungroup k a) = M.Map Ident (Maybe (Ungroup k a -> Ungroup k a))
  u # m = letungroup u m

letungroup
  :: Ord k
  => Ungroup k a -> M.Map Ident (Maybe (Ungroup k a -> Ungroup k a)) -> Ungroup k a
letungroup u m = Ungroup (rest `Update` updated)
  where
    updated = (Defn . Block . M.mapKeysMonotonic Key)
      (M.mapMaybe (fmap (\ f -> (lift . getUngroup) (f u))) m)
    
    rest = (Defn . hide (M.keys m) . selfApp . lift) (getUngroup u)

    -- | Folds over a value to find keys to restrict for an expression.
    --
    -- Can be used as function to construct an expression of the 'left-over' components
    -- assigned to nested ungroup patterns.
    hide :: Foldable f => f Ident -> Closed (Tag k) a -> Closed (Tag k) a
    hide ks e = foldl (\ e k -> e `Fix` Key k) e ks
