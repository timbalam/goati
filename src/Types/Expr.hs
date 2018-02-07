{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Types.Expr
  ( Expr(..)
  , Node(..)
  , Rec(..), toRec, foldMapBoundRec, Var(..)
  , Key(..), ExprK, NodeK, RecK, VarK, ScopeK
  , End(..), fromVoid
  , Ident, Vis(..), Unop(..), Binop(..)
  , module Types.Prim
  )
  where
  

import Types.Parser( Ident, Vis(..), Unop(..), Binop(..) )
import qualified Types.Parser as Parser
import Types.Prim

import Control.Monad ( ap )
import Control.Monad.Trans
import Data.Functor.Classes
import Data.Void
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope( foldMapScope, foldMapBound )


-- | After evaluation no free variables should be left
newtype End f = End { getEnd :: forall a. f a }


fromVoid :: Functor f => f Void -> End f
fromVoid f = End (absurd <$> f)


-- | Interpreted my-language expression
data Expr k a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block [Node k (Rec k (Expr k) a)] (M.Map k (Node k (Rec k (Expr k) a)))
  | Expr k a `At` k
  | Expr k a `Fix` k
  | Expr k a `Update` Expr k a
  | Expr k a `AtPrim` PrimTag
  deriving (Functor, Foldable, Traversable)
  
  
-- | Free with generalised Eq1 and Show1 instances
data Node k a = 
    Closed a
  | Open (M.Map k (Node k a))
  deriving (Functor, Foldable, Traversable)
  
  
newtype Rec k m a = Rec { getRec :: Scope Int (Scope k m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toRec :: Monad m => m (Var k (Var Int a)) -> Rec k m a
toRec = Rec . toScope . toScope


foldMapBoundRec :: (Foldable m, Monoid r) => (k -> r) -> Rec k m a -> r
foldMapBoundRec g = foldMapScope g (foldMap (foldMapBound g)) . unscope
  . getRec

  
-- | Expr instances
instance Ord k => Applicative (Expr k) where
  pure = return
  
  (<*>) = ap
  
instance Ord k => Monad (Expr k) where
  return = Var
  
  String s          >>= _ = String s
  Number d          >>= _ = Number d
  Bool b            >>= _ = Bool b
  Var a             >>= f = f a
  Block en se       >>= f = Block (((>>>= f) <$>) <$> en) (((>>>= f) <$>) <$> se)
  e `At` x          >>= f = (e >>= f) `At` x
  e `Fix` m         >>= f = (e >>= f) `Fix` m
  e `Update` w      >>= f = (e >>= f) `Update` (w >>= f)
  e `AtPrim` x      >>= f = (e >>= f) `AtPrim` x
    
  
instance (Ord k, Eq a) => Eq (Expr k a) where
  (==) = eq1
  
  
instance Ord k => Eq1 (Expr k) where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ena sea)   (Block enb seb)   =
    liftEq f ena enb && liftEq f sea seb
    where f = liftEq (liftEq eq)
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` wa)  (eb `Update` wb)  =
    liftEq eq ea eb && liftEq eq wa wb
  liftEq eq (ea `AtPrim` xa)  (eb `AtPrim` xb)         =
    liftEq eq ea eb && xa == xb
  liftEq _  _                   _               = False
   
   
instance (Ord k, Show k, Show a) => Show (Expr k a) where
  showsPrec = showsPrec1
   
   
instance (Ord k, Show k) => Show1 (Expr k) where
  liftShowsPrec = go where 
    
    go
      :: forall k a. (Ord k, Show k)
      => (Int -> a -> ShowS)
      -> ([a] -> ShowS)
      -> Int -> Expr k a -> ShowS
    go f g i e = case e of
      String s          -> showsUnaryWith showsPrec "String" i s
      Number d          -> showsUnaryWith showsPrec "Number" i d
      Bool b            -> showsUnaryWith showsPrec "Bool" i b
      Var a             -> showsUnaryWith f "Var" i a
      Block en se       -> showsBinaryWith f''' f''' "Block" i en se
      e `At` x          -> showsBinaryWith f' showsPrec "At" i e x
      e `Fix` x         -> showsBinaryWith f' showsPrec "Fix" i e x
      e `Update` w      -> showsBinaryWith f' f' "Update" i e w
      e `AtPrim` p      -> showsBinaryWith f' showsPrec "AtPrim" i e p
      where
        f''' :: (Show1 f, Show1 g, Show1 h) => Int -> f (g (h a)) -> ShowS
        f''' = liftShowsPrec f'' g''
        
        f'' :: (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
        f'' = liftShowsPrec f' g'
        
        g'' :: (Show1 f, Show1 g) => [f (g a)] -> ShowS
        g'' = liftShowList f' g'
        
        f' :: Show1 f => Int -> f a -> ShowS
        f' = liftShowsPrec f g
        
        g' :: Show1 f => [f a] -> ShowS
        g' = liftShowList f g
        
        
-- | Node instances
instance Eq k => Eq1 (Node k) where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open fa)  (Open fb)  = liftEq (liftEq eq) fa fb
  liftEq _  _           _         = False
  
  
instance (Eq k, Eq a) => Eq (Node k a) where
  Closed a == Closed b = a == b
  Open fa  == Open fb  = fa == fb
  _        == _        = False
 

instance Show k => Show1 (Node k) where
  liftShowsPrec f g i (Closed a) = showsUnaryWith f "Closed" i a
  liftShowsPrec f g i (Open m) = showsUnaryWith f'' "Open" i m where
    f'' = liftShowsPrec f' g'
    g' = liftShowList f g
    f' = liftShowsPrec f g
    
    
instance (Show k, Show a) => Show (Node k a) where
  showsPrec d (Closed a) = showParen (d > 10)
    (showString "Closed " . showsPrec 11 a)
  showsPrec d (Open s) = showParen (d > 10)
    (showString "Open " . showsPrec 11 s)
    

-- | Rec instances
instance MonadTrans (Rec k) where
  lift = Rec . lift . lift
  
  
instance Bound (Rec k)
  
  
instance (Show k, Monad m, Show1 m, Show a) => Show (Rec k m a) where
  showsPrec = showsPrec1
    
    
instance (Show k, Monad m, Show1 m) => Show1 (Rec k m) where
  liftShowsPrec f g i m =
    (showsUnaryWith f''' "toRec" i . fromScope . fromScope) (getRec m) where
    f''' = liftShowsPrec  f'' g''
      
    f' = liftShowsPrec f g
    g' = liftShowList f g
    
    f'' = liftShowsPrec f' g'
    g'' = liftShowList f' g'
    
    

-- | Expression key type
data Key k =
    Ident Ident
  | Symbol k
  | Unop Unop
  | Binop Binop
  deriving (Eq, Ord, Show)
  
        
-- | Aliases specialised to Key k
type VarK k = Vis Int (Key k)
type ExprK k = Expr (Key k)
type NodeK k = Node (Key k)
type RecK k = Rec (Key k)
type ScopeK k = Scope (Key k)

    
