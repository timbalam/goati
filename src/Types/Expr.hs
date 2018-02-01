{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Types.Expr
  ( Expr(..)
  , Node(..)
  , Rec(..), toRec, Var(..)
  , Key(..)
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
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope( hoistScope )


-- Interpreted my-language expression
data Expr a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block [Node (Rec Expr a)] (M.Map Key (Node (Rec Expr a)))
  | Expr a `At` Key
  | Expr a `Fix` Key
  | Expr a `Update` Expr a
  | Expr a `AtPrim` PrimTag
  deriving (Functor, Foldable, Traversable)
  
  
-- | Free with generalised Eq1 and Show1 instances
data Node a = 
    Closed a
  | Open (M.Map Key (Node a))
  deriving (Functor, Foldable, Traversable)
  
  
newtype Rec m a = Rec { getRec :: Scope Int (Scope Key m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toRec :: Monad m => m (Var Key (Var Int a)) -> Rec m a
toRec = Rec . toScope . toScope


hoistRec :: Functor f => (forall x . f x -> g x) -> Rec f a -> Rec g a
hoistRec f (Rec s) = Rec (hoistScope (hoistScope f) s)

  
-- | Expr instances
instance Applicative Expr where
  pure = return
  
  (<*>) = ap
  
instance Monad Expr where
  return = Var
  
  String s          >>= _ = String s
  Number d          >>= _ = Number d
  Bool b            >>= _ = Bool b
  Var a             >>= f = f a
  Block en se       >>= f = Block
    ((map . fmap) (>>>= f) en)
    ((fmap . fmap) (>>>= f) se)
  e `At` x          >>= f = (e >>= f) `At` x
  e `Fix` m         >>= f = (e >>= f) `Fix` m
  e `Update` w      >>= f = (e >>= f) `Update` (w >>= f)
  e `AtPrim` x      >>= f = (e >>= f) `AtPrim` x
    
  
instance Eq a => Eq (Expr a) where
  (==) = eq1
  
  
instance Eq1 Expr where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ena sea)   (Block enb seb)   =
    liftEq f ena enb && liftEq f sea seb where
    f = liftEq (liftEq eq)
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` wa)  (eb `Update` wb)  =
    liftEq eq ea eb && liftEq eq wa wb
  liftEq eq (ea `AtPrim` xa)  (eb `AtPrim` xb)         =
    liftEq eq ea eb && xa == xb
  liftEq _  _                   _               = False
   
   
instance Show a => Show (Expr a) where
  showsPrec = showsPrec1
   
   
instance Show1 Expr where
  liftShowsPrec = go where 
    
    go :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Expr a -> ShowS
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
instance Eq1 Node where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open fa)  (Open fb)  = liftEq (liftEq eq) fa fb
  liftEq _  _           _         = False
  
  
instance (Eq a) => Eq (Node a) where
  Closed a == Closed b = a == b
  Open fa  == Open fb  = fa == fb
  _        == _        = False
 

instance Show1 Node where
  liftShowsPrec f g i (Closed a) = showsUnaryWith f "Closed" i a
  liftShowsPrec f g i (Open m) = showsUnaryWith f'' "Open" i m where
    f'' = liftShowsPrec f' g'
    g' = liftShowList f g
    f' = liftShowsPrec f g
    
    
instance (Show a) => Show (Node a) where
  showsPrec d (Closed a) = showParen (d > 10)
    (showString "Closed " . showsPrec 11 a)
  showsPrec d (Open s) = showParen (d > 10)
    (showString "Open " . showsPrec 11 s)
    

-- | Rec instances
instance MonadTrans Rec where
  lift = Rec . lift . lift
  
  
instance Bound Rec
  
  
instance (Monad m, Show1 m, Show a) => Show (Rec m a) where
  showsPrec = showsPrec1
    
    
instance (Monad m, Show1 m) => Show1 (Rec m) where
  liftShowsPrec f g i m =
    (showsUnaryWith f''' "toRec" i . fromScope . fromScope) (getRec m) where
    f''' = liftShowsPrec  f'' g''
      
    f' = liftShowsPrec f g
    g' = liftShowList f g
    
    f'' = liftShowsPrec f' g'
    g'' = liftShowList f' g'
    
    

-- | Expression key type
data Key =
    Ident Ident
  | Symbol Int
  | Unop Unop
  | Binop Binop
  deriving (Eq, Ord, Show)
    
