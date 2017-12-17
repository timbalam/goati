{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Expr
  ( Eval(..)
  , Expr(..)
  , liftExpr
  , mapExpr
  , Enscope(..)
  , Id(..)
  , Result(..)
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
--import Data.Either ( lmap )
import Data.Functor.Classes
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import Bound


lmap :: (a -> b) -> Result a c -> Result b c
lmap f = Result . either (Left . f) Right . getResult


-- Represent an expression with a possibly undefined value
newtype Eval a = Eval { runEval :: Maybe (Expr a) }
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
liftExpr :: Expr a -> Eval a
liftExpr = Eval . return


mapExpr :: (Expr a -> Expr b) -> Eval a -> Eval b
mapExpr f = Eval . fmap f . runEval
  
  
-- Interpreted my-language expression
data Expr a =
    String T.Text
  | Number Double
  | Var a
  | Block [Enscope Eval a] (M.Map (Tag Id) (Enscope Eval a))
  | Expr a `Fix` Tag Id
  | Expr a `At` Tag Id
  | Expr a `Update` Expr a
  | Expr a `Concat` Eval a
  deriving (Eq, Show, Functor, Foldable, Traversable)
            
  
newtype Enscope m a = Enscope { getEnscope :: Scope Int (Scope (Tag Id) m) a }
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  
 
data Id =
    BlockId Integer
  | StrId T.Text
  | FloatId Rational
  | IntId Integer
  deriving (Eq, Ord, Show)
  
  
instance Applicative Eval where
  pure = return
  (<*>) = ap

instance Monad Eval where
  return = Eval . return . return
  
  Eval m >>= f = Eval (m >>= f') where
    f' (String s)        = return (String s)
    f' (Number d)        = return (Number d)
    f' (Var e)           = runEval (f e)
    f' (Block en se)     = return (Block (map (>>>= f) en) (M.map (>>>= f) se))
    f' (v `Fix` x)       = (`Fix` x) <$> f' v
    f' (v `At` x)        = (`At` x)  <$> f' v
    f' (v1 `Update` v2)  = liftA2 Update (f' v1)  (f' v2)
    f' (v `Concat` e)    = (`Concat` (e >>= f)) <$> f' v
    
instance Eq1 Eval where
  liftEq eq (Eval ma) (Eval mb) = liftEq (liftEq eq) ma mb
  
instance Show1 Eval where
  liftShowsPrec f g i (Eval m) =
    showsUnaryWith (liftShowsPrec fval gval) "Eval" i m where
    fval = liftShowsPrec f g
    gval = liftShowList f g
      

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  
  String s        >>= _ = String s
  Number d        >>= _ = Number d
  Var a           >>= f = f a
  Block en se     >>= f =
    Block (map (>>>= liftExpr . f) en) (M.map (>>>= liftExpr . f) se)
  v `At` x        >>= f = (v >>= f) `At` x
  v `Fix` x       >>= f = (v >>= f) `Fix` x
  v `Update` w    >>= f = (v >>= f) `Update` (w >>= f)
  v `Concat` e    >>= f = (v >>= f) `Concat` (e >>= liftExpr . f)
    
instance Eq1 Expr where
  liftEq eq (String sa)         (String sb)         = sa == sb
  liftEq eq (Number da)         (Number db)         = da == db
  liftEq eq (Var a)             (Var b)             = eq a b
  liftEq eq (Block ena sea)     (Block enb seb)     = 
    liftEq (liftEq eq) ena enb && liftEq (liftEq eq) sea seb
    
  liftEq eq (va `At` xa)        (vb `At` xb)        =
    liftEq eq va vb && xa == xb
    
  liftEq eq (va `Fix` xa)       (vb `Fix` xb)       =
    liftEq eq va vb && xa == xb
    
  liftEq eq (va `Update` wa)  (vb `Update` wb)  =
    liftEq eq va vb && liftEq eq wa wb
    
  liftEq eq (va `Concat` ea)  (vb `Concat` eb)  =
    liftEq eq va vb && liftEq eq ea eb
    
  liftEq _  _                   _                  = False
    
instance Show1 Expr where
  liftShowsPrec f g i e = case e of
    String s        -> showsUnaryWith showsPrec "String" i s
    Number d        -> showsUnaryWith showsPrec "Number" i d
    Var a           -> showsUnaryWith f "Var" i a
    Block en se     -> showsBinaryWith flist fmap "Block" i en se
    v `At` x        -> showsBinaryWith fval showsPrec "At" i v x
    v `Fix` x       -> showsBinaryWith fval showsPrec "Fix" i v x
    v `Update` w    -> showsBinaryWith fval fval "Update" i v w
    v `Concat` e    -> showsBinaryWith fval fexpr "Concat" i v e
    where
      fval = liftShowsPrec f g
      flist = liftShowsPrec (liftShowsPrec f g) (liftShowList f g)
      fmap = liftShowsPrec (liftShowsPrec f g) (liftShowList f g)
      fexpr = liftShowsPrec f g

  
instance MonadTrans Enscope where
  lift = Enscope . lift . lift
  
instance Bound Enscope
  
    
-- Either wrapper with specialised Monoid instance
newtype Result a b = Result { getResult :: Either a b }
  deriving (Functor, Applicative, Monad)
  
  
-- Match expression tree
data MTree a = MV a | MT (M.Map (Tag Id) (MTree a))

emptyMTree = MT M.empty


mergeMTree :: MTree a -> MTree a -> Result (PathError Id (Tag Id)) (MTree a)
mergeMTree (MT m) (MT n)  = MT <$> unionAWith f m n where
  f k a b = lmap (k `HasError`) (mergeMTree a b)
mergeMTree _      _       = (Result . Left) ErrorRoot


instance Monoid (Result (DefnError Id (Vis Id)) (MTree b)) where
  mempty = pure emptyMTree
  
  a `mappend` b = join (liftA2 f a b) where
    f a b = lmap OlappedMatch (mergeMTree a b)



-- Set expression tree
data STree a = ST (M.Map a (MTree (Eval a)))

emptySTree = ST M.empty


mergeSTree :: Ord a => STree a -> STree a -> Result (PathError Id a) (STree a)
mergeSTree (ST a) (ST b) = ST <$> unionAWith f a b where
  f k a b = lmap (k `HasError`) (mergeMTree a b)
  
  
instance Ord a => Monoid (Result (DefnError Id a) (STree a)) where
  mempty = pure emptySTree
  
  a `mappend` b = join (liftA2 f a b) where
    f a b = lmap OlappedSet (mergeSTree a b)
  

declSTree :: Path Id a -> STree a
declSTree path = (tree path . MV) (Eval Nothing)
  

pathSTree :: Path Id a -> Eval a -> STree a
pathSTree path = tree path . MV


punSTree :: Path Id a -> STree a
punSTree path = tree path emptyMTree


tree :: Path Id a -> MTree (Eval a) -> STree a
tree = go
  where
    go (Pure a)                     = ST . M.singleton a
    go (Free (path `Parser.At` x))  = go path . MT . M.singleton x

  
pathMTree :: Path Id (Tag Id) -> a -> MTree a
pathMTree path = go path . MV
  where
    go (Pure x)                     = MT . M.singleton x
    go (Free (path `Parser.At` x))  = go path . MT . M.singleton x
      

blockMTree :: Monoid m => (Eval a -> m) -> MTree (Eval a -> m) -> Eval a -> m
blockMTree _ (MV f) e = f e
blockMTree k (MT m) e = (k . Eval) (foldr (fmap . flip Fix) (runEval e) (M.keys m)) <> go (MT m) e
  where
    go :: Monoid m => MTree (Eval a -> m) -> Eval a -> m
    go (MV f) e = f e
    go (MT m) e = M.foldMapWithKey
      (\ k -> (flip go . Eval . fmap (`At` k)) (runEval e))
      m
  

blockSTree :: STree (Vis Id) -> Expr (Vis Id)
blockSTree (ST m) =
  Block (M.elems en) se
  where
    (se, en) =
      M.foldrWithKey
        (\ k a (s, e) -> let
          aen = abstMTree (return k) a
          ase = substitute k (lift (Eval Nothing)) aen
          in case k of
            Priv x -> (s, M.insert x aen e)
            Pub x -> (M.insert x ase s, e))
        (M.empty, M.empty)
        m
        
    abstMTree :: Eval (Vis Id) -> MTree (Eval (Vis Id)) -> Enscope Eval (Vis Id)
    abstMTree _ (MV e) = (Enscope . abstract fenv . abstract fself) e
    abstMTree p (MT m) = (wrap . liftExpr) (Block []
      (M.mapWithKey
        (\ k -> lift . unwrap . abstMTree ((Eval . fmap (`At` k)) 
          (runEval p)))
        m) `Concat` unwrap (lift p')) where
      p' = Eval (foldr (fmap . flip Fix) (runEval p) (M.keys m))
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
    
