{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}
--{#- LANGUAGE UndecidableInstances #-}


-- | Module of my language core data type representation
module My.Types.Repr
  ( Open(..)
  , Closed(..), selfApp
  , Self(..), Super(..), Bindings
  , Prim(..)
  , IOPrimTag(..)
  , Tag(..)
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
import Bound.Scope (mapBound, foldMapScope, abstractEither)



-- | An open expression representing an extensible value
data Open k a =
    Var a
  | Defn (Closed k (Bindings (Open k) a))
    -- ^ Abstract extensible components of a closed expression
  | Let [Scope Int (Open k) a] (Scope Int (Open k) a)
    -- ^ Local recursive definitions
  | Prim (Prim (Open k a))
    -- ^ Primitives
  | Closed k (Open k a) `At` k
  | Closed k (Open k a) `AtPrim` IOPrimTag (Open k Void)
  | Open k a `Update` Open k a
  deriving (Functor, Foldable, Traversable)
  
-- e.g. 
-- Defn (Scope (Var (B Self)) `App` Scope (Var (B Self))) :: Open k a
-- Defn (Scope (Var (B Self)) `App` Scope (Var (B Self))) `App` Var a :: Closed k (Open k) a
-- Var a `App` Var a :: Closed k (Open k) a
  
-- | Closed expression with fixed set of nested open values
data Closed k a =
    a `App` a
    -- ^ Application closes an open expression
  | Block (M.Map k a)
    -- ^ Set of public components
  | Closed k a `Fix` k
  | Closed k a `Concat` Closed k a
  deriving (Functor, Foldable, Traversable)

selfApp :: a -> Closed k a
selfApp m = m `App` m
  
  
-- | Marker type for self- and super- references
data Self = Self deriving (Eq, Show)
data Super = Super deriving (Eq, Show)

type Bindings m = Scope Super (Scope Self m)
  
  
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
  
  Var a          >>= f = f a
  Defn d         >>= f = Defn (fmap (>>>= lift . f) d)
  Let ds d       >>= f = Let (map (>>>= f) ds) (d >>>= f)
  Prim p         >>= f = Prim (fmap (>>= f) p)
  c `At` x       >>= f = (fmap (>>= f) c) `At` x
  c `AtPrim` t   >>= f = (fmap (>>= f) c) `AtPrim` t
  o1 `Update` o2 >>= f = (o1 >>= f) `Update` (o2 >>= f)
    
        
instance (Ord k, Eq a) => Eq (Open k a) where
  (==) = eq1
    
instance Ord k => Eq1 (Closed k) where
  liftEq eq = f where
    f (a1 `App` a2)      (b1 `App` b2)      = eq a1 b1 && eq a2 b2
    f (Block sa)         (Block sb)         = liftEq eq sa sb
    f (ca `Fix` xa)      (cb `Fix` xb)      = liftEq eq ca cb && xa == xb
    f (ca1 `Concat` ca2) (cb1 `Concat` cb2) = liftEq eq ca1 cb1 && liftEq eq ca2 cb2 
    f  _                   _                = False
  
instance Ord k => Eq1 (Open k) where
  liftEq eq = f where
    f (Var a)            (Var b)            = eq a b
    f (Defn da)          (Defn db)          = liftEq (liftEq eq) da db
    f (Let das da)       (Let dbs db)       = liftEq (liftEq eq) das dbs && liftEq eq da db
    f (Prim pa)          (Prim pb)          = liftEq f pa pb
    f (ca `At` xa)       (cb `At` xb)       = f' ca cb && xa == xb
    f (ca `AtPrim` ta)   (cb `AtPrim` tb)   = f' ca cb && ta == tb
    f (oa1 `Update` oa2) (ob1 `Update` ob2) = f oa1 ob1 && f oa2 ob2
    f  _                 _                  = False
    
    f' = liftEq (liftEq eq)
   
   
instance (Ord k, Show k, Show a) => Show (Open k a) where
  showsPrec = showsPrec1
    
instance (Ord k, Show k) => Show1 (Closed k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Closed k a -> ShowS
  liftShowsPrec f g i e = case e of 
    a1 `App` a2    -> showsBinaryWith f f "App" i a1 a2
    Block s        -> showsUnaryWith f' "Block" i s
    c `Fix` k      -> showsBinaryWith f' showsPrec "Fix" i c k
    c1 `Concat` c2 -> showsBinaryWith f' f' "Concat" i c1 c2
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f. Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k) => Show1 (Open k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Open k a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a        -> showsUnaryWith f "Var" i a
    Defn d       -> showsUnaryWith f'' "Defn" i d
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
      
      --g'' = liftShowList f' g'
      --f''' = liftShowsPrec f'' g''
      
      
instance S.Self a => S.Self (Open k a) where
  self_ = Var . S.self_
  
instance S.Local a => S.Local (Open k a) where
  local_ = Var . S.local_
  
instance S.Field (Open (Tag k) a) where
  type Compound (Open (Tag k) a) = Open (Tag k) a
  c #. i = selfApp c `At` Key i
  
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
  
  
-- Manually implemented as monotonicity with Key ordering is relied upon
instance Ord k => Ord (Tag k) where
  compare (Key a)     (Key b)     = compare a b
  compare (Key _)     _           = GT
  compare _           (Key _ )    = LT
  compare (Symbol a)  (Symbol b)  = compare a b
  

    
