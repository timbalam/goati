{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}
--{#- LANGUAGE UndecidableInstances #-}


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
import qualified My.Types.Syntax.Class as S
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
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  

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
  | Builtin BuiltinSymbol
  deriving (Eq, Show)
  
  
data BuiltinSymbol =
    Self
  | SkipAsync
  deriving (Eq, Ord, Show)

  
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
  liftEq eq (ea `At` xa)     (eb `At` xb)     = liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)    (eb `Fix` xb)    = liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` ba) (eb `Update` bb) = liftEq eq ea eb && liftEq eq ba bb
  liftEq eq (ea `AtPrim` pa) (eb `AtPrim` pb) = liftEq eq ea eb && pa == pb
  liftEq _  _                   _               = False
   
instance (Ord k, Show k, Show a) => Show (Expr k a) where
  showsPrec = showsPrec1

instance (Ord k, Show k) => Show1 (Expr k) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Expr k a -> ShowS
  liftShowsPrec f g i e = case e of
    Prim p       -> showsUnaryWith f'' "Prim" i p  
    Var a        -> showsUnaryWith f "Var" i a
    Block d      -> showsUnaryWith f' "Block" i d
    e `At` k     -> showsBinaryWith f' showsPrec "At" i e k
    e `Fix` k    -> showsBinaryWith f' showsPrec "Fix" i e k
    e `Update` d -> showsBinaryWith f' f' "Update" i e d
    e `AtPrim` p -> showsBinaryWith f' showsPrec "AtPrim" i e p
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f. Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance S.Self a => S.Self (Expr k a) where
  self_ = Var . S.self_
  
instance S.Local a => S.Local (Expr k a) where
  local_ = Var . S.local_ 
  
instance S.Field (Expr (Tag k) a) where
  type Compound (Expr (Tag k) a) = Expr (Tag k) a
  
  e #. k = e `At` Key k
  
instance S.Path (Expr (Tag k) a)
  
instance S.Lit (Expr k a) where
  int_ = Prim . Number . fromInteger
  str_ = Prim . String
  num_ = Prim . Number
  
  unop_ op = Prim . Unop op
  binop_ op a b = Prim (Binop op a b)
      
      
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
    
instance Show a => Show (Prim a) where
  showsPrec = showsPrec1
  
instance Show1 Prim where
  liftShowsPrec f g i e = case e of
    Number n     -> showsUnaryWith showsPrec "Number" i n
    String s     -> showsUnaryWith showsPrec "String" i s
    Bool b       -> showsUnaryWith showsPrec "Bool" i b
    IOError e    -> showsUnaryWith showsPrec "IOError" i e
    Unop op e    -> showsBinaryWith showsPrec f "Unop" i op e
    Binop op e w -> showParen (i > 10)
      (showString "Binop " . showsPrec 11 op . showChar ' ' . f 11 e
        . showChar ' ' . f 11 w)
    
    
instance Show (IOPrimTag a) where
  showsPrec i _ = errorWithoutStackTrace "show: IOPrimTag"
       
        
instance Ord k => Bound (Defns k) where
  Defns en se >>>= f = Defns (((>>>= f) <$>) <$> en) (((>>>= f) <$>) <$> se)

instance (Ord k, Eq1 m, Monad m) => Eq1 (Defns k m) where
  liftEq eq (Defns ena sea) (Defns enb seb) =
    liftEq f ena enb && liftEq f sea seb
    where f = liftEq (liftEq eq)
        
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Defns k m) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Defns k m a -> ShowS
  liftShowsPrec f g i (Defns en se) =
    showsBinaryWith f''' f''' "Defns" i en se
    where
      f' :: forall f . Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
      g'' :: forall f g. (Show1 f, Show1 g) => [f (g a)] -> ShowS
      g'' = liftShowList f' g'
      
      f'''
        :: forall f g h. (Show1 f, Show1 g, Show1 h)
        => Int -> f (g (h a)) -> ShowS
      f''' = liftShowsPrec f'' g''
        
instance (Eq k, Eq a) => Eq (Node k a) where
  (==) = eq1
        
instance Eq k => Eq1 (Node k) where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open fa)  (Open fb)  = liftEq (liftEq eq) fa fb
  liftEq _  _           _         = False

instance (Show k, Show a) => Show (Node k a) where
  showsPrec = showsPrec1
  
instance Show k => Show1 (Node k) where
  liftShowsPrec f g i (Closed a) = showsUnaryWith f "Closed" i a
  liftShowsPrec f g i (Open m) = showsUnaryWith f'' "Open" i m
    where
      f' = liftShowsPrec f g
      g' = liftShowList f g
      f'' = liftShowsPrec f' g'


instance MonadTrans (Rec k) where
  lift = Rec . lift . lift
  
instance Bound (Rec k)
  
  
-- Manually implemented as monotonicity with Key ordering is relied upon
instance Ord k => Ord (Tag k) where
  compare (Key a)     (Key b)     = compare a b
  compare (Key _)     _           = GT
  compare _           (Key _ )    = LT
  compare (Symbol a)  (Symbol b)  = compare a b
  compare (Symbol _)  _           = GT
  compare _           (Symbol _)  = LT
  compare (Builtin a) (Builtin b) = compare a b
  
  
instance S.Self a => S.Self (Nec a) where
  self_ = Nec Req . S.self_
  
instance S.Local a => S.Local (Nec a) where
  local_ = Nec Req . S.local_
  

    
