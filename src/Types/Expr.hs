{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving #-}
module Types.Expr
  ( Expr(..)
  , Member(..)
  , Id(..)
  , MTree, pathMTree, blockMTree
  , STree, declSTree, pathSTree, punSTree, blockSTree
  , Vid, Tid
  , ExprErrors
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
import Bound.Scope( transverseScope, abstractEither )


-- Interpreted my-language expression
data Expr a =
    String T.Text
  | Number Double
  | Undef Vid
  | Var a
  | Block [MTree (Scope Int Member a)] (M.Map Tid (MTree (Scope Int Member a)))
  | Expr a `At` Tid
  | Expr a `Fix` Tid
  | Expr a `Update` Expr a
  deriving (Eq, Show, Functor, Foldable, Traversable)

  
newtype Member a = Member { getMember :: Scope Tid Expr a }
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  
 
data Id =
    BlockId Integer
  | StrId T.Text
  | FloatId Rational
  | IntId Integer
  deriving (Eq, Ord, Show)
  

-- type aliases  
type Vid = Vis Id
type Tid = Tag Id
type ExprErrors a = NonEmpty (ExprError Id a)
  

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  
  String s      >>= _ = String s
  Number d      >>= _ = Number d
  Undef a       >>= _ = Undef a
  Var a         >>= f = f a
  Block en se   >>= f = Block
    ((map . fmap) (>>>= Member . lift . f) en)
    ((M.map . fmap) (>>>= Member . lift . f) se)
  e `At` x      >>= f = (e >>= f) `At` x
  e `Fix` x     >>= f = (e >>= f) `Fix` x
  e `Update` w  >>= f = (e >>= f) `Update` (w >>= f)
        
    
instance Eq1 Expr where
  liftEq eq (String sa)       (String sb)       = sa == sb
  liftEq eq (Number da)       (Number db)       = da == db
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Undef a)         (Undef b)         = a == b
  liftEq eq (Block ena sea)   (Block enb seb)   = 
    (liftEq . liftEq) (liftEq eq) ena enb &&
    (liftEq . liftEq) (liftEq eq) sea seb
  liftEq eq (va `At` xa)      (vb `At` xb)      =
    liftEq eq va vb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (va `Update` wa)  (vb `Update` wb)  =
    liftEq eq va vb && liftEq eq wa wb
  liftEq _  _                   _                  = False
    
instance Show1 Expr where
  liftShowsPrec f g i e = case e of
    String s        -> showsUnaryWith showsPrec "String" i s
    Number d        -> showsUnaryWith showsPrec "Number" i d
    Undef a         -> showsUnaryWith showsPrec "Undef" i a
    Var a           -> showsUnaryWith f "Var" i a
    Block en se     -> showsBinaryWith flist fmap "Block" i en se
    e `At` x        -> showsBinaryWith fexpr showsPrec "At" i e x
    e `Fix` x       -> showsBinaryWith (liftShowsPrec f g)
      showsPrec "Fix" i e x
    e `Update` w    -> showsBinaryWith fexpr fexpr "Update" i e w
    where
      flist = liftShowsPrec fmtree gmtree
      fmap = liftShowsPrec fmtree gmtree
      fmtree = liftShowsPrec fsc gsc
      gmtree = liftShowList fsc gsc
      fsc = liftShowsPrec f g
      gsc = liftShowList f g
      fexpr = liftShowsPrec f g
  
  
-- Match expression tree
data MTree a = MV a | MT (M.Map (Tag Id) (MTree a))
  deriving (Eq, Show, Functor, Foldable, Traversable)

emptyMTree = MT M.empty


mergeMTree :: MTree a -> MTree a -> Collect (PathError Id Tid) (MTree a)
mergeMTree (MT m) (MT n)  = MT <$> unionAWith f m n where
  f k a b = first (PathError . M.singleton k) (mergeMTree a b)
mergeMTree _      _       = (Collect . Left) (PathError M.empty)


instance Eq1 MTree where
  liftEq eq (MV a) (MV b) = eq a b
  liftEq eq (MT ma) (MT mb) = liftEq (liftEq eq) ma mb

  
instance Show1 MTree where
  liftShowsPrec f g i e = case e of
    MV a -> showsUnaryWith f "MV" i a
    MT m -> showsUnaryWith (liftShowsPrec f' g') "MT" i m where
      f' = liftShowsPrec f g
      g' = liftShowList f g
  

instance Monoid (Collect (ExprErrors b) (MTree a)) where
  mempty = pure emptyMTree
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeMTree a b))


-- Set expression tree
newtype STree a = ST (M.Map a (MTree (Maybe (Expr a))))

emptySTree = ST M.empty


mergeSTree :: Ord a => STree a -> STree a -> Collect (PathError Id a) (STree a)
mergeSTree (ST a) (ST b) = ST <$> unionAWith f a b where
  f k a b = first (PathError . M.singleton k) (mergeMTree a b)
  
  
instance Ord a => Monoid (Collect (ExprErrors a) (STree a)) where
  mempty = pure emptySTree
  
  a `mappend` b = either 
    (Collect . Left)
    (first (pure . OlappedSet))
    (getCollect (liftA2 mergeSTree a b))
  

declSTree :: Path Id Vid -> STree Vid
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

  
pathMTree :: Path Id Tid -> a -> MTree a
pathMTree path = go path . MV
  where
    go (Pure x)                     = MT . M.singleton x
    go (Free (path `Parser.At` x))  = go path . MT . M.singleton x
      

blockMTree :: Monoid m => (Expr a -> m) -> MTree (Expr a -> m) -> Expr a -> m
blockMTree _ (MV f) e = f e
blockMTree k (MT m) e = k (foldr (flip Fix) e (M.keys m)) <> go (MT m) e
  where
    go :: Monoid m => MTree (Expr a -> m) -> Expr a -> m
    go (MV f) e = f e
    go (MT m) e = M.foldMapWithKey
      (\ k -> flip go (e `At` k))
      m
      
      
blockSTree :: STree Vid -> Expr Label
blockSTree (ST m) =
  Block (M.elems en) se
  where
    (se, en) = M.foldrWithKey
      (\ k a (s, e) -> let a' = abstMTree k a in case k of
        Priv x -> (s, M.insert x a' e)
        Pub x  -> (M.insert x a' s, e))
      (M.empty, M.empty)
      m
        
    abstMTree :: Vid -> MTree (Maybe (Expr Vid))
      -> MTree (Scope Int Member Label)
    abstMTree k (MV e) = MV (maybe
      (liftExpr (Undef k))
      (abstract fenv . Member . abstractEither fself)
      e)
      
    abstMTree _ (MT m) = MT (M.mapWithKey (abstMTree . Pub) m)
    
    liftExpr :: MonadTrans t => Expr a -> t Member a
    liftExpr = lift . Member . lift
        
    fself :: Vid -> Either Tid Label
    fself (Pub x)               = Left x
    fself (Priv l)
        | M.member (Label l) se = Left (Label l)
        | otherwise             = Right l
      
    fenv :: Label -> Maybe Int
    fenv l = M.lookupIndex l en
        
  
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
