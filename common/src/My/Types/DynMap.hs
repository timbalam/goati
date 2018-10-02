{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

module My.Types.DynMap
  where
  
  
import My.Types.Error
import My.Types.Paths.Patt
import qualified My.Types.Syntax as P
import qualified My.Types.Syntax.Class as S
import My.Util (Compose(..))
import Control.Applicative (liftA2)
import Control.Comonad.Cofree
import Control.Monad.Writer
import Control.Monad.Trans.Free
import qualified Data.Map as M
import Prelude.Extras
  
  
data DynMap k a = DynMap (Maybe (DynError k)) (M.Map k a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
instance Show k => Show1 (DynMap k) where
  showsPrec1 = showsPrec
  
instance Eq k => Eq1 (DynMap k) where
  (==#) = (==)
  
type Dyn k = Compose (DynMap k) (Free (DynMap k))

  
unionWith
  :: Ord k
  => (Free (DynMap k) a -> Free (DynMap k) a -> Free (DynMap k) a)
  -> Dyn k a -> Dyn k a -> Dyn k a
unionWith f (Compose (DynMap e kva)) (Compose (DynMap Nothing kvb)) = 
  Compose (DynMap e (M.unionWith f kva kvb))
unionWith _ _ d = d
  
throwDyn :: DynError k -> Compose (DynMap k) f a
throwDyn e = Compose (DynMap (Just e) M.empty)
    
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
      . getCompose
      . throwDyn) (StaticError e)

dynCheckDecomp
  :: MonadWriter [StaticError k] f
  => Decomps k (f a) -> f (Dyn k a)
dynCheckDecomp (Compose (Comps kv)) = Compose . DynMap Nothing <$>
  M.traverseWithKey
    (\ k -> check k . dynCheckNode check)
    kv
  where
    check = dynCheckStmts OlappedMatch

dynCheckPatt
  :: MonadWriter [StaticError k] f
  => Patt (Decomps k) a
  -> f (Patt (Dyn k) a)
dynCheckPatt (a :< Decomp cs) =
  (a :<) . Decomp <$>
    traverse (dynCheckDecomp . fmap dynCheckPatt) cs

dynCheckTup
  :: MonadWriter [StaticError k] f
  => Comps k (Node k (f a))
  -> f (M.Map k (Free (DynMap k) a))
dynCheckTup (Comps kv) = M.traverseWithKey
  (\ k -> check k . dynCheckNode check)
  kv
  where
    check = dynCheckStmts (OlappedSet . P.Pub)
      
      
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
              . getCompose
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