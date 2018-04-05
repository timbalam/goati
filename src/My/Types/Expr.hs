{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}

-- | Module of my language core expression data types

module My.Types.Expr
  ( Expr(..)
  , Prim(..)
  , Defns(..)
  , Node(..)
  , Rec(..), toRec, foldMapBoundRec, abstractRec
  , Tag(..)
  , End(..), fromVoid
  , Ident, Key(..), Unop(..), Binop(..)
  , Var(..), Bound(..), Scope(..)
  , Nec(..), NecType(..)
  , module My.Types.Prim
  )
  where
  

import My.Types.Parser (Ident, Key(..), Unop(..), Binop(..))
import qualified My.Types.Parser as Parser
import My.Types.Prim
import Control.Monad (ap)
import Control.Monad.Trans
import Data.Functor.Classes
import Data.Void
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope (foldMapScope, foldMapBound, abstractEither)


-- | Represents expression without free variables
newtype End f = End { getEnd :: forall a. f a }


fromVoid :: Functor f => f Void -> End f
fromVoid f = End (absurd <$> f)


-- | Interpreted my language expression
data Expr k a =
    Var a
  | Block (Defns k (Expr k) a)
  | Expr k a `At` k
  | Expr k a `Fix` k
  | Expr k a `Update` Defns k (Expr k) a
  | Prim (Prim (Expr k a))
  deriving (Functor, Foldable, Traversable)
  
  
-- | My language primitives
data Prim a =
    Number Double
  | String T.Text
  | Bool Bool
  | Unop Unop a
  | Binop Binop a a
  deriving (Functor, Foldable, Traversable)
  
  
-- | Set of recursive, extensible definitions / parameter bindings
data Defns k m a =
  Defns
    [Node k (Rec k m a)]
    -- ^ List of local defintions
    (M.Map k (Node k (Rec k m a)))
    -- ^ Publicly visible definitions
  deriving (Functor, Foldable, Traversable)
  
  
-- | Free (Map k) with generalised Eq1 and Show1 instances
-- 
--   Can be a closed leaf value or an open tree of paths representing
--   the defined parts of an incomplete value
data Node k a = 
    Closed a
  | Open (M.Map k (Node k a))
  deriving (Functor, Foldable, Traversable)
  
  
-- | Wraps bindings for a pair of scopes as contained by 'Defns'. 
--    * The outer scope represents indices into the list of private local 
--      definitions
--    * The inner scope represents names of the publicly visible definitions
--      (acting like a self-reference in a class method)
newtype Rec k m a = Rec { getRec :: Scope Int (Scope k m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

-- | Construct a 'Rec' from a classic de Bruijn representation
toRec :: Monad m => m (Var k (Var Int a)) -> Rec k m a
toRec = Rec . toScope . toScope


-- | Fold over bound keys in a 'Rec'  
foldMapBoundRec :: (Foldable m, Monoid r) => (k -> r) -> Rec k m a -> r
foldMapBoundRec g = foldMapScope g (foldMap (foldMapBound g)) . unscope
  . getRec
  
  
-- | Abstract an expression into a 'Rec'
abstractRec
  :: Monad m
  => (b -> Either Int c)
  -- ^ abstract public/env bound variables
  -> (a -> Either k b)
  -- ^ abstract private/self bound variables
  -> m a
  -- ^ Expression
  -> Rec k m c
  -- ^ Expression with bound variables
abstractRec f g = Rec . abstractEither f . abstractEither g

  
instance Ord k => Applicative (Expr k) where
  pure = return
  
  (<*>) = ap
  
instance Ord k => Monad (Expr k) where
  return = Var
  
  Var a             >>= f = f a
  Block b           >>= f = Block (b >>>= f)
  e `At` x          >>= f = (e >>= f) `At` x
  e `Fix` m         >>= f = (e >>= f) `Fix` m
  e `Update` b      >>= f = (e >>= f) `Update` (b >>>= f) 
  Prim p            >>= f = Prim ((>>= f) <$> p)
  
  
instance (Ord k, Eq a) => Eq (Expr k a) where
  (==) = eq1
  
  
instance Ord k => Eq1 (Expr k) where
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ba)        (Block bb)        = liftEq eq ba bb
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` ba)  (eb `Update` bb)  =
    liftEq eq ea eb && liftEq eq ba bb
  liftEq eq (Prim pa)         (Prim pb)         = liftEq (liftEq eq) pa pb
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
      Var a             -> showsUnaryWith f "Var" i a
      Block b           -> showsUnaryWith f' "Block" i b
      e `At` x          -> showsBinaryWith f' showsPrec "At" i e x
      e `Fix` x         -> showsBinaryWith f' showsPrec "Fix" i e x
      e `Update` b      -> showsBinaryWith f' f' "Update" i e b
      Prim p            -> showsUnaryWith f'' "Prim" i p
      where
        f' :: Show1 f => Int -> f a -> ShowS
        f' = liftShowsPrec f g
        
        g' :: Show1 f => [f a] -> ShowS
        g' = liftShowList f g
        
        f'' :: (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
        f'' = liftShowsPrec f' g'

  
instance Eq1 Prim where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Unop opa a)      (Unop opb b)      = opa == opb && eq a b
  liftEq eq (Binop opa la ra) (Binop opb lb rb) = opa == opb &&
    eq la lb && eq ra rb
        

instance Show1 Prim where
  liftShowsPrec f g i e = case e of
    String s     -> showsUnaryWith showsPrec "String" i s
    Number d     -> showsUnaryWith showsPrec "Number" i d
    Bool b       -> showsUnaryWith showsPrec "Bool" i b
    Unop op e    -> showsBinaryWith showsPrec f "Unop" i op e
    Binop op l r -> showParen (i > 10)
      (showString "Binop " . showsPrec 11 op . showChar ' '
        . f 11 l . showChar ' ' . f 11 r)
        
        
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
    
  
-- | Possibly unbound variable
-- 
--   An variable with 'Opt' 'NecType' that is unbound at the top level of
--   a program will be substituted by an empty value
data Nec a = Nec NecType a
  deriving (Eq, Ord, Show)
    
    
-- | Binding status indicator
data NecType = Req | Opt
  deriving (Eq, Ord, Show)
    
    
-- | Expression key type
data Tag k =
    Key Key
  | Symbol k
  deriving (Eq, Show)
  
  
-- Manually implemented as monotonicity with Key ordering is relied upon
instance Ord k => Ord (Tag k) where
  compare (Key a)    (Key b)    = compare a b
  compare (Key _)    _          = GT
  compare _          (Key _ )   = LT
  compare (Symbol a) (Symbol b) = compare a b
  compare (Symbol _) _          = GT
  compare _          (Symbol _) = LT
  

    
