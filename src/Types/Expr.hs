{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes #-}
module Types.Expr
  ( Expr(..)
  , liftExpr
  , mapExpr
  , Enscope(..)
  , Id(..)
  , MTree
  , pathMTree
  , blockMTree
  , STree
  , declSTree
  , pathSTree
  , punSTree
  , blockSTree
  , Vis(..)
  , Label
  , Tag(..)
  , Path
  )
  where
  

import Types.Parser( Label, Tag(..), Path, Vis(..) )
import qualified Types.Parser as Parser
import Types.Error

import Control.Applicative ( liftA2 )
import Control.Monad ( join, ap )
import Control.Monad.Free
import Control.Monad.Trans
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
data Expr a =
    Val (Val a)
  | Var a
  | Expr a `Fix` Tag Id
  

data Val a =
    String T.Text
  | Number Double
  | Block [Enscope Expr a] (M.Map (Tag Id) (Maybe (Enscope Expr a)))
  | Expr a `At` Tag Id
  | Expr a `Update` Expr a
  | Expr a `Concat` Expr a
  deriving (Eq, Show, Functor, Foldable, Traversable)
  

newtype Eval a = Eval { getEval :: Maybe (Expr a) }
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
liftExpr = Extn . return
  
  
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
  
  
instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  
  Val v     >>= f = Val (case v of
    String s      -> String s
    Number d      -> Number d
    Block en sa   -> Block (map (>>>= f) en) (M.map (>>>= f) se)
    e `At` x      -> (e >>= f) `At` x
    e `Update` w  -> (e >>= f) `Update` (w >>= f)
    e `Concat` w  -> (e >>= f) `Concat` (w >>= f))
  Var a     >>= f = f a
  e `Fix` x >>= f = (e >>= f) `Fix` x
    
instance Eq1 Expr where
  liftEq eq (Val va)      (Val vb)      = liftEq eq va vb
  liftEq eq (Var a)       (Var b)       = da == db
  liftEq eq (ea `Fix` xa) (eb `Fix` xb) = liftEq eq ea ab && xa == xb
  liftEq _  _                   _                  = False
    
instance Show1 Expr where
  liftShowsPrec f g i e = case e of
    Val v     -> showsUnaryWith (liftShowsPrec f g) "Val" i v
    Var a     -> showsUnaryWith showsPrec "Var" i d
    e `Fix` x -> showsBinaryWith (liftShowsPrec f g) showsPrec "Fix" i e x
    
      
instance Eq1 Val where
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
    
instance Show1 Val where
  liftShowsPrec f g i e = case e of
    String s        -> showsUnaryWith showsPrec "String" i s
    Number d        -> showsUnaryWith showsPrec "Number" i d
    Block en se     -> showsBinaryWith flist fmap "Block" i en se
    e `At` x        -> showsBinaryWith fexpr showsPrec "At" i e x
    e `Update` w    -> showsBinaryWith fexpr fexpr "Update" i e w
    e `Concat` w    -> showsBinaryWith fexpr fexpr "Concat" i e w
    where
      flist = liftShowsPrec fsc gsc
      fmap = liftShowsPrec (liftShowsPrec fsc gsc) (liftShowList fsc gsc)
      fsc = liftShowsPrec f g
      gsc = liftShowList f g
      fexpr = liftShowsPrec f g
      --fext = liftShowsPrec f g

  
instance MonadTrans Enscope where
  lift = Enscope . lift . lift
  
instance Bound Enscope


undefined :: a -> Expr (Maybe a) -> Maybe (Expr (Maybe a))
undefined me = go where
  go (Var a) = Just (Var (if a == me then Nothing else Just a))
  go (Val v) = case v of
    
    String s -> Just (String s)
    Number d -> Just (Number d)
    B
  
  
-- Match expression tree
data MTree a = MV a | MT (M.Map (Tag Id) (MTree a))

emptyMTree = MT M.empty


mergeMTree :: MTree a -> MTree a -> Collect (PathError Id (Tag Id)) (MTree a)
mergeMTree (MT m) (MT n)  = MT <$> unionAWith f m n where
  f k a b = first (PathError . M.singleton k) (mergeMTree a b)
mergeMTree _      _       = (Collect . Left) (PathError M.empty)


instance Monoid (Collect (NonEmpty (DefnError Id b)) (MTree b)) where
  mempty = pure emptyMTree
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeMTree a b))



-- Set expression tree
data STree a = ST (M.Map a (MTree (Maybe (Expr a))))

emptySTree = ST M.empty


mergeSTree :: Ord a => STree a -> STree a -> Collect (PathError Id a) (STree a)
mergeSTree (ST a) (ST b) = ST <$> unionAWith f a b where
  f k a b = first (PathError . M.singleton k) (mergeMTree a b)
  
  
instance Ord a => Monoid (Collect (NonEmpty (DefnError Id a)) (STree a)) where
  mempty = pure emptySTree
  
  a `mappend` b = either 
    (Collect . Left)
    (first (pure . OlappedSet))
    (getCollect (liftA2 mergeSTree a b))
  

declSTree :: Path Id (Vis Id) -> STree (Vis Id)
declSTree path = tree path (MV Nothing)


pathSTree :: Path Id a -> Expr a -> STree a
pathSTree path = tree path . MV . Just


punSTree :: Path Id a -> STree a
punSTree path = tree path emptyMTree


tree :: Path Id a -> MTree (Maybe (Expr a)) -> STree a
tree = go
  where
    go (Pure a)                     = ST . M.singleton a
    go (Free (path `Parser.At` x))  = go path . MT . M.singleton x

  
pathMTree :: Path Id (Tag Id) -> a -> MTree a
pathMTree path = go path . MV
  where
    go (Pure x)                     = MT . M.singleton x
    go (Free (path `Parser.At` x))  = go path . MT . M.singleton x
      

blockMTree :: Monoid m => (Maybe (Fixed Expr a) -> m) -> MTree (Maybe (Fixed Expr a) -> m) -> Maybe (Fixed Expr a) -> m
blockMTree _ (MV f) e = f e
blockMTree k (MT m) e = k (e `Fixed` (s <> M.keysSet m)) e <> go (MT m) e
  where
    go :: Monoid m => MTree (Maybe (Expr a) -> m) -> Maybe (Expr a) -> m
    go (MV f) e = f e
    go (MT m) e = M.foldMapWithKey
      (\ k -> flip go ((`At` k) <$> e))
      m
  

blockSTree :: STree (Vis Id) -> Collect (NonEmpty (Vis Id)) (Expr (Vis Id))
blockSTree (ST m) =
  Block (M.elems en) se
  where
    (se, en) =
      M.foldrWithKey
        (\ k a (s, e) -> let
          aen = abstMTree (return k) a
          ase = substitute k (lift Nothing) aen
          in case k of
            Priv x -> (s, M.insert x aen e)
            Pub x -> (M.insert x ase s, e))
        (M.empty, M.empty)
        m
        
    abstMTree :: Exten (Vis Id) -> MTree (Exten (Vis Id)) -> Enscope Exten (Vis Id)
    abstMTree _ (MV e) = (Enscope . abstract fenv . abstract fself) e
    abstMTree p (MT m) = (wrap . liftExpr) (Block []
      (M.mapWithKey
        (\ k -> lift . unwrap . abstMTree ((Exten . fmap (`At` k)) 
          (runExten p)))
        m) `Concat` unwrap (lift p')) where
      p' = Exten (foldr (fmap . flip Fixed) (runExten p) (M.keys m))
      unwrap = unscope . unscope . getEnscope
      wrap = Enscope . Scope . Scope
        
    -- unscope (unscope (getEnscope (Enscope f a)))
    --  ~ unscope (unscope (Scope1 (Scope2 f) a)) 
    --  ~ unscope (Scope2 f (Var b1 (Scope2 f a)))
    --  ~ f (Var b2 (f (Var b1 (Scope2 f))))
        
        
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
    
