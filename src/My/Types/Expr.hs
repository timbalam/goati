{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}

-- | Module of my language core expression data types

module My.Types.Expr
  ( Expr(..)
  , Prim(..)
  , IOPrimTag(..)
  , Defns(..)
  , Node(..)
  , Rec(..), toRec, foldMapBoundRec, abstractRec
  , Tag(..)
  , BuiltinSymbol(..)
  , Ident, Key(..), Unop(..), Binop(..)
  , Var(..), Bound(..), Scope(..)
  , Nec(..), NecType(..)
  )
  where
  

import My.Types.Parser (Ident, Key(..), Unop(..), Binop(..))
import qualified My.Types.Parser as Parser
import My.Types.Eval (Comp(..))
import Control.Monad (ap)
import Control.Monad.Trans
import Control.Exception (IOException)
import Data.Functor.Classes
import Data.Void
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Data.IORef (IORef)
import System.IO (Handle, IOMode)
import Bound
import Bound.Scope (foldMapScope, foldMapBound, abstractEither)



-- | Interpreted my language expression
data Expr k a =
    Prim (Prim (Expr k a))
  | Var a
  | Block (Defns k (Expr k) a)
  | Expr k a `At` k
  | Expr k a `Fix` k
  | Expr k a `Update` Defns k (Expr k) a
  | Expr k a `AtPrim` (IOPrimTag (Expr k Void))
  deriving (Functor, Foldable, Traversable)
  
  
-- | My language primitives
data Prim a =
    Number Double
  | String T.Text
  | Bool Bool
  | IOError IOException
  | Unop Unop a
  | Binop Binop a a
  deriving (Functor, Foldable, Traversable)
  
  
-- | Primitive my language field tags
data IOPrimTag a =
    OpenFile IOMode
  | HGetLine Handle
  | HGetContents Handle
  | HPutStr Handle
  | NewMut
  | GetMut (IORef a)
  | SetMut (IORef a)
  deriving Eq
  
  
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
  
  Prim p       >>= f = Prim ((>>= f) <$> p)
  Var a        >>= f = f a
  Block b      >>= f = Block (b >>>= f)
  e `At` x     >>= f = (e >>= f) `At` x
  e `Fix` m    >>= f = (e >>= f) `Fix` m
  e `Update` b >>= f = (e >>= f) `Update` (b >>>= f)
  e `AtPrim` p >>= f = (e >>= f) `AtPrim` p
  
  
instance (Ord k, Eq a) => Eq (Expr k a) where
  (==) = eq1
  
  
instance Ord k => Eq1 (Expr k) where
  liftEq eq (Prim pa)        (Prim pb)        = liftEq (liftEq eq) pa pb
  liftEq eq (Var a)          (Var b)          = eq a b
  liftEq eq (Block ba)       (Block bb)       = liftEq eq ba bb
  liftEq eq (ea `At` xa)     (eb `At` xb)     = liftEq eq ea eb &&
    xa == xb
  liftEq eq (ea `Fix` xa)    (eb `Fix` xb)    = liftEq eq ea eb &&
    xa == xb
  liftEq eq (ea `Update` ba) (eb `Update` bb) = liftEq eq ea eb &&
    liftEq eq ba bb
  liftEq eq (ea `AtPrim` pa) (eb `AtPrim` pb) = liftEq eq ea eb && pa == pb
  liftEq _  _                   _               = False
   

instance Eq a => Eq (Prim a) where
  (==) = eq1
        
instance Eq1 Prim where
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq _  (IOError ea)      (IOError eb)      = ea == eb
  liftEq eq (Unop opa ea)     (Unop opb eb)     = opa == opb && eq ea eb
  liftEq eq (Binop opa ea wa) (Binop opb eb wb) = opa == opb && eq ea eb
    && eq wa wb
       
        
instance Ord k => Bound (Defns k) where
  Defns en se >>>= f = Defns (((>>>= f) <$>) <$> en) (((>>>= f) <$>) <$> se)
  
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Defns k m) where
  liftEq eq (Defns ena sea) (Defns enb seb) =
    liftEq f ena enb && liftEq f sea seb
    where f = liftEq (liftEq eq)
          
        
instance Eq k => Eq1 (Node k) where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open fa)  (Open fb)  = liftEq (liftEq eq) fa fb
  liftEq _  _           _         = False
  
  
instance (Eq k, Eq a) => Eq (Node k a) where
  Closed a == Closed b = a == b
  Open fa  == Open fb  = fa == fb
  _        == _        = False
 

instance MonadTrans (Rec k) where
  lift = Rec . lift . lift
  
  
instance Bound (Rec k)
    
  
-- | Possibly unbound variable
-- 
--   An variable with 'Opt' 'NecType' that is unbound at the top level of
--   a program will be substituted by an empty value
data Nec a = Nec NecType a
  deriving (Eq, Ord)
    
    
-- | Binding status indicator
data NecType = Req | Opt
  deriving (Eq, Ord)
    
    
-- | Expression key type
data Tag k =
    Key Key
  | Symbol k
  | Builtin BuiltinSymbol
  deriving (Eq)
  
  
data BuiltinSymbol =
    Self
  | SkipAsync
  deriving (Eq, Ord)
  
  
-- Manually implemented as monotonicity with Key ordering is relied upon
instance Ord k => Ord (Tag k) where
  compare (Key a)     (Key b)     = compare a b
  compare (Key _)     _           = GT
  compare _           (Key _ )    = LT
  compare (Symbol a)  (Symbol b)  = compare a b
  compare (Symbol _)  _           = GT
  compare _           (Symbol _)  = LT
  compare (Builtin a) (Builtin b) = compare a b
  

    
