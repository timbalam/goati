{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Types.Expr
  ( Expr(..)
  , Defns(..)
  , Node(..)
  , Rec(..), toRec, foldMapBoundRec, abstractRec
  , Key(..), ExprK, DefnsK, NodeK, RecK, VarK, ScopeK, VarResK
  , End(..), fromVoid
  , Ident, Res(..), Vis(..), Import(..), Unop(..), Binop(..)
  , Var(..), Bound(..)
  , module Types.Prim
  )
  where
  

import Types.Parser( Ident, Res(..), Vis(..), Import(..), Unop(..), Binop(..) )
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
import Bound.Scope( foldMapScope, foldMapBound, abstractEither )


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
  | Block (Defns k (Expr k) a)
  | Expr k a `At` k
  | Expr k a `Fix` k
  | Expr k a `Update` Defns k (Expr k) a
  | Expr k a `AtPrim` PrimTag
  deriving (Functor, Foldable, Traversable)
  
  
-- | Set of recursive, extensible definitions
data Defns k m a =
  Defns [Node k (Rec k m a)] (M.Map k (Node k (Rec k m a)))
  deriving (Functor, Foldable, Traversable)
  
  
-- | Free with generalised Eq1 and Show1 instances
data Node k a = 
    Closed a
  | Open (M.Map k (Node k a))
  deriving (Functor, Foldable, Traversable)
  
  
-- | Wrapper for dual env and self scopes
newtype Rec k m a = Rec { getRec :: Scope Int (Scope k m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toRec :: Monad m => m (Var k (Var Int a)) -> Rec k m a
toRec = Rec . toScope . toScope


foldMapBoundRec :: (Foldable m, Monoid r) => (k -> r) -> Rec k m a -> r
foldMapBoundRec g = foldMapScope g (foldMap (foldMapBound g)) . unscope
  . getRec
  
  
abstractRec
  :: Monad m => (b -> Either Int c) -> (a -> Either k b) -> m a -> Rec k m c
abstractRec f g = Rec . abstractEither f . abstractEither g

  
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
  Block b           >>= f = Block (b >>>= f)
  e `At` x          >>= f = (e >>= f) `At` x
  e `Fix` m         >>= f = (e >>= f) `Fix` m
  e `Update` b      >>= f = (e >>= f) `Update` (b >>>= f)
  e `AtPrim` x      >>= f = (e >>= f) `AtPrim` x
  
  
instance (Ord k, Eq a) => Eq (Expr k a) where
  (==) = eq1
  
  
instance Ord k => Eq1 (Expr k) where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ba)        (Block bb)        = liftEq eq ba bb
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` ba)  (eb `Update` bb)  =
    liftEq eq ea eb && liftEq eq ba bb
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
      Block b           -> showsUnaryWith f' "Block" i b
      e `At` x          -> showsBinaryWith f' showsPrec "At" i e x
      e `Fix` x         -> showsBinaryWith f' showsPrec "Fix" i e x
      e `Update` b      -> showsBinaryWith f' f' "Update" i e b
      e `AtPrim` p      -> showsBinaryWith f' showsPrec "AtPrim" i e p
      where
        f' :: Show1 f => Int -> f a -> ShowS
        f' = liftShowsPrec f g
        
        
-- | Defns instances
instance Ord k => Bound (Defns k) where
  Defns en se >>>= f = Defns (((>>>= f) <$>) <$> en) (((>>>= f) <$>) <$> se)
  
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Defns k m) where
  liftEq eq (Defns ena sea) (Defns enb seb) =
    liftEq f ena enb && liftEq f sea seb
    where f = liftEq (liftEq eq)
    
    
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Defns k m) where
  liftShowsPrec f g i (Defns en se) = showsBinaryWith (liftShowsPrec f'' g'')
    (liftShowsPrec f'' g'') "Defns" i en se where
        f'' = liftShowsPrec f' g'
        g'' = liftShowList f' g'
        f' = liftShowsPrec f g
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
type ExprK k = Expr (Key k)
type DefnsK k = Defns (Key k)
type NodeK k = Node (Key k)
type RecK k = Rec (Key k)
type ScopeK k = Scope (Key k)
type VarK k = Vis Ident (Key k)
type VarResK k = Res Import (VarK k)

    
