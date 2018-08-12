{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}

-- | Module of my language core data type representation
module My.Types.Repr
  ( Open(..), Defn(..), Closed(..)
  , Prim(..)
  , IOPrimTag(..)
  , Tag(..)
  , Self(..), Super(..)
  , Nec(..), nec
  , S.Ident, S.Unop(..), S.Binop(..)
  , Var(..), Bound(..), Scope(..)
  )
  where
  

import qualified My.Types.Syntax.Class as S
import Control.Monad (ap)
import Control.Monad.Trans
import Control.Exception (IOException)
import Data.Bifoldable (bifoldMap)
import Data.Functor.Classes
import Data.IORef (IORef)
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Set as S
import Data.String (IsString(..))
import qualified Data.Text as T
import Data.Void
import System.IO (Handle, IOMode)
import Bound
import Bound.Scope (hoistScope)


-- | Runtime value representation
data Open k a =
    Var a
  | Val (Scope Super (Defn k) a)
    -- ^ An extensible value with memoised current value
  | Let [Scope Int (Open k) a] (Scope Int (Open k) a)
    -- ^ Local recursive definitions
  | Prim (Prim (Open k a))
    -- ^ Primitives
  | Closed k a `At` k
  | Closed k a `AtPrim` IOPrimTag (Open k Void)
  deriving (Functor, Foldable, Traversable)
  
data Defn k a =
    Defn (Open k a)
  | Block (M.Map k (Scope Self (Open k) a))
    -- ^ Set of public components
  | Defn k a `Fix` k
  | Defn k a `Update` Open k a
    -- ^ Bind 'super' value
  deriving (Functor, Foldable, Traversable)
  
-- | Fixed set of nested values
data Closed k a =
    Closed (Open k a)
  | Defn k a `App` Open k a
    -- ^ Bind 'self' value
  | Compound (M.Map k (Open k a))
  | Closed k a `Concat` Closed k a
  deriving (Functor, Foldable, Traversable)
  
  
-- | Marker type for self- and super- references
data Self = Self deriving (Eq, Show)
data Super = Super deriving (Eq, Show)
  
-- | My language primitives
data Prim a =
    Number Double
  | Text T.Text
  | Bool Bool
  | IOError IOException
  | Unop S.Unop a
  | Binop S.Binop a a
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
  
  
-- | Expression key type
data Tag k =
    Key S.Ident
  | Symbol k
  deriving (Eq, Show)
  
  
data Nec a = Req a | Opt a

nec :: (a -> b) -> (a -> b) -> Nec a -> b
nec f g (Req a) = f a
nec f g (Opt a) = g a
  
  
instance Ord k => Applicative (Open k) where
  pure = Var
  (<*>) = ap
  
instance Ord k => Monad (Open k) where
  return = pure
  
  e >>= f = case e of
    Var a        -> f a
    Val s        -> Val (s >>= lift . f')
    Let ds d     -> Let (map (>>>= f) ds) (d >>>= f)
    Prim p       -> Prim (fmap (>>= f) p)
    c `At` x     -> (bindClosed f c) `At` x
    c `AtPrim` t -> (bindClosed f c) `AtPrim` t
    where
      f' = Defn . f
      
      bindClosed f (Closed o)       = Closed (o >>= f)
      bindClosed f (d `App` o)      = (d >>= f') `App` (o >>= f)
      bindClosed f (Compound b)     = Compound (M.map (>>= f) b)
      bindClosed f (c1 `Concat` c2) = bindClosed f c1 `Concat` bindClosed f c2
  
instance Ord k => Applicative (Defn k) where
  pure = Defn . pure
  (<*>) = ap
  
instance Ord k => Monad (Defn k) where
  return = pure
  
  d >>= f = case d of
    Defn o       -> Defn (o >>= f')
    Block b      -> Block (M.map (>>>= f') b)
    d `Fix` x    -> (d >>= f) `Fix` x
    d `Update` o -> (d >>= f) `Update` (o >>= f')
    where
      f' = Val . lift . f
      

instance (Ord k, Eq a) => Eq (Open k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Open k) where
  liftEq eq = f where
    f (Var a)          (Var b)          = eq a b
    f (Val s1)         (Val s2)         = liftEq eq s1 s2
    f (Let ds1 d1)     (Let ds2 d2)     = liftEq (liftEq eq) ds1 ds2 && liftEq eq d1 d2
    f (Prim p1)        (Prim p2)        = liftEq (liftEq eq) p1 p2
    f (c1 `At` x1)     (c2 `At` x2)     = liftEq eq c1 c2 && x1 == x2
    f (c1 `AtPrim` t1) (c2 `AtPrim` t2) = liftEq eq c1 c2 && t1 == t2
    f _                _                = False
   
instance Ord k => Eq1 (Defn k) where
  liftEq eq = f where
    f (Defn e1)        (Defn e2)        = liftEq eq e1 e2
    f (Block b1)       (Block b2)       = liftEq (liftEq eq) b1 b2
    f (c1 `Fix` x1)    (c2 `Fix` x2)    = liftEq eq c1 c2 && x1 == x2
    f (d1 `Update` e1) (d2 `Update` e2) = liftEq eq d1 d2 && liftEq eq e1 e2
    f  _               _                = False
    
instance Ord k => Eq1 (Closed k) where
  liftEq eq = f where
    f (Closed o1)   (Closed o2)         = liftEq eq o1 o2
    f (d1 `App` o1) (d2 `App` o2)       = liftEq eq d1 d2 && liftEq eq o1 o2
    f (Compound b1) (Compound b2)       = liftEq (liftEq eq) b1 b2
    f (c1 `Concat` v1) (c2 `Concat` v2) = liftEq eq c1 c2 && liftEq eq v1 v2 
   
instance (Ord k, Show k, Show a) => Show (Open k a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Open k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Open k a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a        -> showsUnaryWith f "Var" i a
    Val s        -> showsUnaryWith f' "Val" i s
    Let d ds     -> showsBinaryWith f'' f' "Let" i d ds
    Prim p       -> showsUnaryWith f'' "Prim" i p
    c `At` k     -> showsBinaryWith f' showsPrec "At" i c k 
    c `AtPrim` p -> showsBinaryWith f' showsPrec "AtPrim" i c p
    where 
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k) => Show1 (Defn k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Defn k a -> ShowS
  liftShowsPrec f g i e = case e of 
    Defn e         -> showsUnaryWith f' "Defn" i e
    Block b        -> showsUnaryWith f'' "Block" i b
    c `Fix` k      -> showsBinaryWith f' showsPrec "Fix" i c k
    d `Update` e -> showsBinaryWith f' f' "Update" i d e
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f. Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k) => Show1 (Closed k) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Closed k a -> ShowS
  liftShowsPrec f g i e = case e of
    Closed o       -> showsUnaryWith f' "Closed" i o
    d `App` o      -> showsBinaryWith f' f' "App" i d o
    Compound b     -> showsUnaryWith f'' "Compound" i b
    c1 `Concat` c2 -> showsBinaryWith f' f' "Concat" i c1 c2
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' = liftShowsPrec f' g'
      
      
instance S.Self a => S.Self (Open k a) where
  self_ = Var . S.self_
  
instance S.Local a => S.Local (Open k a) where
  local_ = Var . S.local_
  
instance S.Field (Open (Tag k) a) where
  type Compound (Open (Tag k) a) = Open (Tag k) a
  o #. i = (Defn o `App` o) `At` Key i
  
nume = error "Num (Open k a)"

instance Num (Open k a) where
  fromInteger = Prim . Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Fractional (Open k a)"

instance Fractional (Open k a) where
  fromRational = Prim . Number . fromRational
  (/) = frace
  
instance IsString (Open k a) where
  fromString = Prim . Text . fromString

instance S.Lit (Open k a) where
  unop_ op = Prim . Unop op
  binop_ op a b = Prim (Binop op a b)
      
      
instance Eq a => Eq (Prim a) where
  (==) = eq1
        
instance Eq1 Prim where
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Text sa)         (Text sb)         = sa == sb
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
    Text s       -> showsUnaryWith showsPrec "Text" i s
    Bool b       -> showsUnaryWith showsPrec "Bool" i b
    IOError e    -> showsUnaryWith showsPrec "IOError" i e
    Unop op e    -> showsBinaryWith showsPrec f "Unop" i op e
    Binop op e w -> showParen (i > 10)
      (showString "Binop " . showsPrec 11 op . showChar ' ' . f 11 e
        . showChar ' ' . f 11 w)
    
    
instance Show (IOPrimTag a) where
  showsPrec i _ = errorWithoutStackTrace "show: IOPrimTag"
  
  
instance S.Local a => S.Local (Nec a) where local_ = Req . S.local_
instance S.Self a => S.Self (Nec a) where self_ = Req . S.self_
  
-- Manually implemented as monotonicity with Key ordering is relied upon
instance Ord k => Ord (Tag k) where
  compare (Key a)     (Key b)     = compare a b
  compare (Key _)     _           = GT
  compare _           (Key _ )    = LT
  compare (Symbol a)  (Symbol b)  = compare a b
  

    
