{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

-- | This module implements some data types and definitions for represent Goat values that track errors dynamically.
-- It defines a data type 'DynMap': a wrapper for 'Data.Map' that can respond to missing field requests with a dynamic error,
-- and a type alias 'Dyn': a possibly effectful tree of nested 'DynMaps'.
module Goat.Dyn.DynMap
  where
  
  
import Goat.Error
import Goat.Syntax.Patterns
import qualified Goat.Syntax.Syntax as P
import qualified Goat.Syntax.Class as S
import Goat.Util (Compose(..), (<&>))
import Control.Applicative (liftA2)
import Control.Comonad.Cofree
import Control.Monad.Writer
import Control.Monad.Trans.Free
import Data.Functor.Identity (Identity(..))
import qualified Data.Map as M
import Prelude.Extras
  
  
data DynMap k a = DynMap (Maybe (DynError k)) (M.Map k a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
instance Show k => Show1 (DynMap k) where
  showsPrec1 = showsPrec
  
instance Eq k => Eq1 (DynMap k) where
  (==#) = (==)
  
type Dyn k f = Compose f (Compose (DynMap k) (Free (DynMap k)))
type Dyn' k = Dyn k Identity

dyn :: Applicative f => DynMap k (Free (DynMap k) a) -> Dyn k f a
dyn = Compose . pure . Compose

runDyn' :: Dyn' k a -> DynMap k (Free (DynMap k) a)
runDyn' = getCompose . runIdentity . getCompose

unionWith
  :: (Ord k, Applicative f)
  => (Free (DynMap k) a -> Free (DynMap k) a -> Free (DynMap k) a)
  -> Dyn k f a -> Dyn k f a -> Dyn k f a
unionWith f (Compose m) (Compose m') =
  Compose (liftA2 unionWith' m m') where
    unionWith' (Compose (DynMap e kv))
      (Compose (DynMap Nothing kv')) =
        Compose (DynMap e (M.unionWith f kv kv'))
    unionWith' _ d = d
  
throwDyn :: Applicative f => DynError k -> Dyn k f a
throwDyn e = dyn (DynMap (Just e) M.empty)
    
pruneDyn
  :: (a -> Maybe b)
  -> Free (DynMap k) a -> Maybe (Free (DynMap k) b)
pruneDyn f = go where
  go = iter pruneMap . fmap (fmap pure . f)
  
  pruneMap
    :: DynMap k (Maybe (Free (DynMap k) b))
    -> Maybe (Free (DynMap k) b)
  pruneMap (DynMap e kv) =
    maybeWrap (DynMap e (M.mapMaybe id kv))
    
  maybeWrap (DynMap Nothing kv) | M.null kv = Nothing
  maybeWrap d                               = Just (wrap d)

 
dynCheckNode
  :: Applicative f
  => (k -> ([f a], f (Free (DynMap k) a)) -> f (Free (DynMap k) a))
  -> Node k (f a) -> ([f a], f (Free (DynMap k) a))
dynCheckNode check (Node m) = iterT freeDyn (fmap (fmap pure) m)
  where
    freeDyn = pure . fmap (wrap . DynMap Nothing)
        . M.traverseWithKey check

dynCheckStmts
  :: MonadWriter [StaticError k] f
  => (n -> DefnError k)
  -> n -> ([f b], f (Free (DynMap k) a))
  -> (f (Free (DynMap k) a))
dynCheckStmts throw n pp = case pp of
  ([], m) -> m
  (as, m) -> let e = DefnError (throw n) in
    tell [e] >> m >> sequenceA as >> (return . wrap
      . runDyn' . throwDyn) (StaticError e)

dynCheckDecomp
  :: MonadWriter [StaticError k] f
  => Decomps k (f a)
  -> f (Dyn' k a)
dynCheckDecomp (Compose (Comps kv)) = dyn . DynMap Nothing <$>
  M.traverseWithKey
    (\ k -> check k . dynCheckNode check)
    kv
  where
    check = dynCheckStmts OlappedMatch

dynCheckPatt
  :: MonadWriter [StaticError k] f
  => Patt (Decomps k) a
  -> f (Patt (Dyn' k) a)
dynCheckPatt (a :< Decomp cs) =
  (a :<) . Decomp <$>
    traverse (dynCheckDecomp . fmap dynCheckPatt) cs

dynCheckTup
  :: MonadWriter [StaticError k] f
  => Comps k (Node k (f (Maybe a)))
  -> f (M.Map k (Free (DynMap k) a))
dynCheckTup (Comps kv) = M.traverseWithKey
  (\ k -> check k . dynCheckNode check)
  kv <&> pruneMap
  where
    check = dynCheckStmts (OlappedSet . P.Pub)
    pruneMap = M.mapMaybe (pruneDyn id)
      
      
dynCheckVis
  :: (S.Self k, Ord k, MonadWriter [StaticError k] f)
  => Vis k (Node k (Maybe a))
  -> f (Vis k (Free (DynMap k) a))
dynCheckVis (Vis{private=l,public=s}) =
  liftA2 prunedVis
    (dynCheckPrivate l)
    (checkVis dupl <*> dynCheckPublic s)
  where
    dupl =
      M.filterWithKey
        (\ n _ -> S.self_ n `M.member` s)
        l
        
    prunedVis l s = Vis
      { private = pruneMap (M.difference l dupl)
      , public = pruneMap s
      }
    
    pruneMap :: M.Map i (Free (DynMap k) (Maybe a))
      -> M.Map i (Free (DynMap k) a)
    pruneMap = M.mapMaybe (pruneDyn id)

      
    dynCheckPrivate
      :: (Ord k, MonadWriter [StaticError k] f)
      => M.Map S.Ident (Node k a)
      -> f (M.Map S.Ident (Free (DynMap k) a))  
    dynCheckPrivate = M.traverseWithKey
      (\ n -> checkPriv n . dynCheckNode checkPub
        . fmap pure)
      
    dynCheckPublic
      :: (Ord k, MonadWriter [StaticError k] f)
      => M.Map k (Node k a)
      -> f (M.Map k (Free (DynMap k) a))
    dynCheckPublic = M.traverseWithKey
      (\ k -> checkPub k . dynCheckNode checkPub
        . fmap pure)
      
    checkVis dupl = writer (f, es)
      where
        (Endo f, es) = M.foldMapWithKey
          (\ n _ -> let e = DefnError (OlappedVis n) in
            ((Endo . M.insert (S.self_ n)
              . wrap
              . runDyn'
              . throwDyn) (StaticError e), [e]))
          dupl
          
    checkPriv
      :: MonadWriter [StaticError k] f
      => S.Ident -> ([f a], f (Free (DynMap k) a))
      -> f (Free (DynMap k) a)
    checkPriv = dynCheckStmts (OlappedSet . P.Priv)
    
    checkPub
      :: MonadWriter [StaticError k] f
      => k -> ([f a], f (Free (DynMap k) a))
      -> f (Free (DynMap k) a)
    checkPub = dynCheckStmts (OlappedSet . P.Pub)