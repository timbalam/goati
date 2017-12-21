{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving #-}
module Types.Expr
  ( Expr(..)
  , Eval(..)
  , liftExpr, liftVal
  , MonadExpr(..)
  , Val(..)
  , Enscope(..)
  , Elem
  , Id(..)
  , MTree, pathMTree, blockMTree
  , STree, declSTree, pathSTree, punSTree, blockSTree
  , Expr', STree', Elem'
  , Vis(..), Label, Tag(..), Path
  )
  where
  

import Types.Parser( Label, Tag(..), Path, Vis(..) )
import qualified Types.Parser as Parser
import Types.Error

import Control.Applicative ( liftA2 )
import Control.Monad ( join, ap )
import Control.Monad.Free
import Control.Monad.Trans
import Data.Functor.Identity
import Data.Monoid ( (<>) )
import Data.Bifunctor
import Data.Functor.Classes
import Data.List.NonEmpty( NonEmpty )
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope( transverseScope )


-- Interpreted my-language expression
data Expr m a =
    Val (Val m a)
  | Var a
  | Expr m a `Fix` Tag Id
  deriving (Functor, Foldable, Traversable)
  
deriving instance (Eq a, Eq b) => Eq (Expr (Either b) a)
deriving instance Eq a => Eq (Expr Identity a)
deriving instance (Show a, Show b) => Show (Expr (Either b) a)
deriving instance Show a => Show (Expr Identity a)


data Eval m a = Eval { runEval :: m (Expr m a) }
  deriving (Functor, Foldable, Traversable)

deriving instance (Eq a, Eq b) => Eq (Eval (Either b) a)
deriving instance Eq a => Eq (Eval Identity a)
deriving instance (Show a, Show b) => Show (Eval (Either b) a)
deriving instance Show a => Show (Eval Identity a)

liftExpr :: Monad m => Expr m a -> Eval m a
liftExpr = Eval . return


liftVal :: Monad m => Val m a -> Eval m a
liftVal = liftExpr . Val


class Monad m => MonadExpr m where
  exprConcat :: Eval m a -> Eval m a -> Eval m a
  
  
instance MonadExpr (Either b) where
  exprConcat e (Eval w) = either (const e) (liftVal . Concat e) w
  

instance MonadExpr Identity where
  exprConcat e (Eval w) = (liftVal . Concat e) (runIdentity w)


data Val m a =
    String T.Text
  | Number Double
  | Block [Enscope (Eval m) a] (M.Map (Tag Id) (Elem m a))
  | Eval m a `At` Tag Id
  | Eval m a `Update` Eval m a
  | Eval m a `Concat` Expr m a
  deriving (Functor, Foldable, Traversable)
  

deriving instance (Eq a, Eq b) => Eq (Val (Either b) a)
deriving instance Eq a => Eq (Val Identity a)
deriving instance (Show a, Show b) => Show (Val (Either b) a)
deriving instance Show a => Show (Val Identity a)


type Elem m a = Maybe (Enscope (Eval m) a)

  
newtype Enscope m a = Enscope { getEnscope :: Scope Int (Scope (Tag Id) m) a }
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  
  
transverseEnscope :: (Applicative f, Monad f, Traversable g) => (forall r. g r -> f (h r)) -> Enscope g a -> f (Enscope h a)
transverseEnscope f (Enscope (Scope e)) =
  Enscope . Scope <$> (traverse (traverse tau') e >>= tau') where
  tau' = transverseScope f
  
 
data Id =
    BlockId Integer
  | StrId T.Text
  | FloatId Rational
  | IntId Integer
  deriving (Eq, Ord, Show)
  
  
instance MonadExpr m => Applicative (Eval m) where
  pure = return
  (<*>) = ap

instance MonadExpr m => Monad (Eval m) where
  return = Eval . return . Var
  
  Eval m >>= f = Eval (m >>= f') where
    --f' :: Monad m => Expr m a -> m (Expr m b)
    f' (Val v) = bindVal v
    f' (Var a) = runEval (f a)
    f' (e `Fix` x) = (`Fix` x) <$> f' e
  
    --bindVal :: Monad m => Val m a -> m (Expr m b)
    bindVal (String s)     = (return . Val) (String s)
    bindVal (Number d)     = (return . Val) (Number d)
    bindVal (Block en se)  = (return . Val) (Block (map (>>>= f) en) ((M.map . fmap) (>>>= f) se))
    bindVal (e `At` x)     = (return . Val) ((e >>= f) `At` x)
    bindVal (e `Update` w) = (return . Val) ((e >>= f) `Update` (w >>= f))
    bindVal (e `Concat` w) = (runEval . exprConcat (e >>= f) . Eval) (f' w)
        
    
instance (MonadExpr m, Eq1 m) => Eq1 (Expr m) where
  liftEq eq (Val va)      (Val vb)      = liftEq eq va vb
  liftEq eq (Var a)       (Var b)       = eq a b
  liftEq eq (ea `Fix` xa) (eb `Fix` xb) = liftEq eq ea eb && xa == xb
  liftEq _  _                   _                  = False
    
instance Show1 m => Show1 (Expr m) where
  liftShowsPrec f g i e = case e of
    Val v     -> showsUnaryWith (liftShowsPrec f g) "Val" i v
    Var a     -> showsUnaryWith f "Var" i a
    e `Fix` x -> showsBinaryWith (liftShowsPrec f g) showsPrec "Fix" i e x
    
    
instance (MonadExpr m, Eq1 m) => Eq1 (Eval m) where
  liftEq eq (Eval ma) (Eval mb) = liftEq (liftEq eq) ma mb
  
instance Show1 m => Show1 (Eval m) where
  liftShowsPrec f g i (Eval m) = showsUnaryWith (liftShowsPrec f' g') "Eval" i m where
    f' = liftShowsPrec f g
    g' = liftShowList f g
    
    
instance (MonadExpr m, Eq1 m) => Eq1 (Val m) where
  liftEq eq (String sa)         (String sb)         = sa == sb
  liftEq eq (Number da)         (Number db)         = da == db
  liftEq eq (Block ena sea)     (Block enb seb)     = 
    liftEq (liftEq eq) ena enb &&
    (liftEq . liftEq) (liftEq eq) sea seb
    
  liftEq eq (va `At` xa)        (vb `At` xb)        =
    liftEq eq va vb && xa == xb
    
  liftEq eq (va `Update` wa)  (vb `Update` wb)  =
    liftEq eq va vb && liftEq eq wa wb
    
  liftEq eq (va `Concat` ea)  (vb `Concat` eb)  =
    liftEq eq va vb && liftEq eq ea eb
    
  liftEq _  _                   _                  = False
    
instance Show1 m => Show1 (Val m) where
  liftShowsPrec f g i e = case e of
    String s        -> showsUnaryWith showsPrec "String" i s
    Number d        -> showsUnaryWith showsPrec "Number" i d
    Block en se     -> showsBinaryWith flist fmap "Block" i en se
    e `At` x        -> showsBinaryWith feval showsPrec "At" i e x
    e `Update` w    -> showsBinaryWith feval feval "Update" i e w
    e `Concat` w    -> showsBinaryWith feval fexpr "Concat" i e w
    where
      flist = liftShowsPrec fsc gsc
      fmap = liftShowsPrec (liftShowsPrec fsc gsc) (liftShowList fsc gsc)
      fsc = liftShowsPrec f g
      gsc = liftShowList f g
      feval = liftShowsPrec f g
      fexpr = liftShowsPrec f g

  
instance MonadTrans Enscope where
  lift = Enscope . lift . lift
  
instance Bound Enscope
  
  
-- Match expression tree
data MTree a = MV a | MT (M.Map (Tag Id) (MTree a))

emptyMTree = MT M.empty


mergeMTree :: MTree a -> MTree a -> Collect (PathError Id (Tag Id)) (MTree a)
mergeMTree (MT m) (MT n)  = MT <$> unionAWith f m n where
  f k a b = first (PathError . M.singleton k) (mergeMTree a b)
mergeMTree _      _       = (Collect . Left) (PathError M.empty)


type Errors a = NonEmpty (DefnError Id a)


instance Monoid (Collect (Errors b) (MTree a)) where
  mempty = pure emptyMTree
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeMTree a b))



-- Set expression tree
data STree m a = ST (M.Map a (MTree (Maybe (Expr m a))))

emptySTree = ST M.empty


mergeSTree :: Ord a => STree m a -> STree m a -> Collect (PathError Id a) (STree m a)
mergeSTree (ST a) (ST b) = ST <$> unionAWith f a b where
  f k a b = first (PathError . M.singleton k) (mergeMTree a b)
  
  
instance Ord a => Monoid (Collect (Errors a) (STree m a)) where
  mempty = pure emptySTree
  
  a `mappend` b = either 
    (Collect . Left)
    (first (pure . OlappedSet))
    (getCollect (liftA2 mergeSTree a b))
  

declSTree :: Path Id (Vis Id) -> STree m (Vis Id)
declSTree path = tree path (MV Nothing)


pathSTree :: Path Id a -> Expr m a -> STree m a
pathSTree path = tree path . MV . Just


punSTree :: Path Id a -> STree m a
punSTree path = tree path emptyMTree


tree :: Path Id a -> MTree (Maybe (Expr m a)) -> STree m a
tree = go
  where
    go (Pure a)                     = ST . M.singleton a
    go (Free (path `Parser.At` x))  = go path . MT . M.singleton x

  
pathMTree :: Path Id (Tag Id) -> a -> MTree a
pathMTree path = go path . MV
  where
    go (Pure x)                     = MT . M.singleton x
    go (Free (path `Parser.At` x))  = go path . MT . M.singleton x
      

blockMTree :: (Monad f, Monoid m) => (Expr f a -> m) -> MTree (Expr f a -> m) -> Expr f a -> m
blockMTree _ (MV f) e = f e
blockMTree k (MT m) e = k (foldr (flip Fix) e (M.keys m)) <> go (MT m) e
  where
    go :: (Monad f, Monoid m) => MTree (Expr f a -> m) -> Expr f a -> m
    go (MV f) e = f e
    go (MT m) e = M.foldMapWithKey
      (\ k -> flip go (Val (liftExpr e `At` k)))
      m

      
type STree' = STree (Either (Vis Id)) (Vis Id)

type Expr' = Expr (Either (Vis Id)) (Vis Id)

type Elem' = Elem (Either (Vis Id)) (Vis Id)
      
      
blockSTree :: STree' -> Expr'
blockSTree (ST m) =
  Val (Block (M.elems en) se)
  where
    (se, en, ks) =
      M.foldrWithKey
        (\ k a (s, e, ks) -> let 
          a' = abstMTree (Var k) a
          in case k of
            Priv x -> case a' of
              Nothing -> (s, e, k:ks)
              Just ea -> (s, M.insert x (unbound ks ea) e, ks)
            Pub x  -> (M.insert x (unbound (k:ks) <$> a') s, e, ks))
        (M.empty, M.empty, [])
        m
        
    abstMTree :: Expr' -> MTree (Maybe Expr') -> Elem'
    abstMTree _ (MV e) =
      Enscope . abstract fenv . abstract fself . liftExpr <$> e
      
    abstMTree p (MT m) = (Just . wrap . exprConcat b . unwrap)
      (lift p') where
      b = liftVal (Block [] (M.mapWithKey
        (\ k -> fmap (lift . unwrap)
          . abstMTree (Val (liftExpr p `At` k)))
        m))
        
      p' = liftExpr (foldr (flip Fix) p (M.keys m))
      
      unwrap = unscope . unscope . getEnscope
      wrap = Enscope . Scope . Scope
  
  
    unbound :: Eq a => [a] -> Enscope (Eval (Either a)) a -> Enscope (Eval (Either a)) a
    unbound ks e = e >>= \ a -> if a `elem` ks then (lift . Eval) (Left a) else return a
        
        
    fself :: Vis Id -> Maybe (Tag Id)
    fself (Pub x)               = Just x
    fself (Priv l)
        | M.member (Label l) se = Just (Label l)
        | otherwise             = Nothing
      
      
    fenv :: Vis Id -> Maybe Int
    fenv (Pub _) = Nothing
    fenv (Priv l) = M.lookupIndex l en
        
  
  
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
