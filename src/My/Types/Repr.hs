{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}
--{#- LANGUAGE UndecidableInstances #-}


-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..), Cached(..)
  , Prim(..)
  , IOPrimTag(..)
  , Tag(..)
  , Ref(..), ref
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
data Repr k a =
    Var a
  | Val (Cached k (Repr k a)) (Super (Repr k) a)
    -- ^ An extensible value with memoised current value
  | Let [Scope Int (Repr k) a] (Scope Int (Repr k) a)
    -- ^ Local recursive definitions
  | Prim (Prim (Repr k a))
    -- ^ Primitives
  | Cached k (Repr k a) `At` k
  | Cached k (Repr k a) `AtPrim` IOPrimTag (Repr k Void)
  | Repr k a `Update` Repr k a
    -- ^ Bind 'super' value
  deriving (Functor, Foldable, Traversable)
  
  
-- | Fixed set of nested values
data Cached k a =
    Cached a
  | a `App` a
    -- ^ Bind 'self' value
  | Block (M.Map k a)
    -- ^ Set of public components
  | Cached k a `Fix` k
  | Cached k a `Concat` Cached k a
  deriving (Functor, Foldable, Traversable)
  
  
-- | Marker type for self- and super- references
newtype Super m a = Super (Scope () (Self m) a)
  deriving (Eq, Show, Eq1, Show1, Functor, Applicative, Monad, MonadTrans, Bound)
  
newtype Self m a =
    Self (Scope () m a)
  | Self m a `Sconcat` Self m a
  deriving (Functor, Foldable, Traversable)
  
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
  
  
instance Ord k => Applicative (Repr k) where
  pure = Var
  (<*>) = ap
  
instance Ord k => Monad (Repr k) where
  return = pure
  
  Var a          >>= f = f a
  Val c e        >>= f = Val (fmap (>>= f) c) (e >>>= f)
  Let ds d       >>= f = Let (map (>>>= f) ds) (d >>>= f)
  Prim p         >>= f = Prim (fmap (>>= f) p)
  c `At` x       >>= f = (fmap (>>= f) c) `At` x
  c `AtPrim` t   >>= f = (fmap (>>= f) c) `AtPrim` t
  e1 `Update` e2 >>= f = (e1 >>= f) `Update` (e2 >>= f)
    
        
instance (Ord k, Eq a) => Eq (Repr k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Repr k) where
  liftEq eq = f where
    f (Var a)          (Var b)          = eq a b
    f (Val c1 e1)      (Val c2 e2)      = liftEq (liftEq eq) c1 c2 && liftEq eq e1 e2
    f (Let ds1 d1)     (Let ds2 d2)     = liftEq (liftEq eq) ds1 ds2 && liftEq eq d1 d2
    f (Prim p1)        (Prim p2)        = liftEq (liftEq eq) p1 p2
    f (c1 `At` x1)     (c2 `At` x2)     = liftEq (liftEq eq) c1 c2 && x1 == x2
    f (c1 `AtPrim` t1) (c2 `AtPrim` t2) = liftEq (liftEq eq) c1 c2 && t1 == t2
    f (e1 `Update` w1) (e2 `Update` w2) = liftEq eq e1 e2 && liftEq eq w1 w2
    f _                _                = False
   
instance (Ord k) => Eq1 (Cached k) where
  liftEq eq = f where
    f (Cached e1)      (Cached e2)      = eq e1 e2
    f (a1 `App` a2)    (b1 `App` b2)    = eq a1 b1 && eq a2 b2
    f (Block m1)       (Block m2)       = liftEq eq m1 m2
    f (c1 `Fix` x1)    (c2 `Fix` x2)    = liftEq eq c1 c2 && x1 == x2
    f (c1 `Concat` v1) (c2 `Concat` v2) = liftEq eq c1 c2 && liftEq eq v1 v2 
    f  _               _                = False
   
instance (Ord k, Show k, Show a) => Show (Repr k a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Repr k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Repr k a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a        -> showsUnaryWith f "Var" i a
    Val c e      -> showsBinaryWith f'' f' "Val" i c e
    Let d ds     -> showsBinaryWith f'' f' "Let" i d ds
    Prim p       -> showsUnaryWith f'' "Prim" i p
    c `At` k     -> showsBinaryWith f'' showsPrec "At" i c k 
    c `AtPrim` p -> showsBinaryWith f'' showsPrec "AtPrim" i c p
    e `Update` w -> showsBinaryWith f' f' "Update" i e w
    where 
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k) => Show1 (Cached k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Cached k a -> ShowS
  liftShowsPrec f g i e = case e of 
    Cached e       -> showsUnaryWith f "Cached" i e
    e `App` w      -> showsBinaryWith f f "App" i e w
    Block m        -> showsUnaryWith f' "Block" i m
    c `Fix` k      -> showsBinaryWith f' showsPrec "Fix" i c k
    c1 `Concat` c2 -> showsBinaryWith f' f' "Concat" i c1 c2
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f. Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance S.Self a => S.Self (Repr k a) where
  self_ = Var . S.self_
  
instance S.Local a => S.Local (Repr k a) where
  local_ = Var . S.local_
  
instance S.Field (Repr (Tag k) a) where
  type Compound (Repr (Tag k) a) = Repr (Tag k) a
  c #. i = Cached c `At` Key i
  
nume = error "Num (Repr k a)"

instance Num (Repr k a) where
  fromInteger = Prim . Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Fractional (Repr k a)"

instance Fractional (Repr k a) where
  fromRational = Prim . Number . fromRational
  (/) = frace
  
instance IsString (Repr k a) where
  fromString = Prim . Text . fromString

instance S.Lit (Repr k a) where
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
  

    
