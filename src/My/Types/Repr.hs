{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}
--{#- LANGUAGE UndecidableInstances #-}


-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..), Open(..), Closed(..)
  , reprOpen, reprClosed, hoistOpen, hoistClosed
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


-- | A value with a dual representation
data Repr k a =
    Var a
  | Val (Closed k (Repr k) a) (Open k (Repr k) a)
  | Let [Scope Int (Repr k) a] (Scope Int (Repr k) a)
    -- ^ Local recursive definitions
  | Prim (Prim (Repr k a))
    -- ^ Primitives
  | Closed k (Repr k) a `At` k
  | Closed k (Repr k) a `AtPrim` IOPrimTag (Repr k Void)
  deriving (Functor, Foldable, Traversable)
  

-- | An open expression representing an extensible value
data Open k m a =
    Open (m a)
  | Defn (Closed k (Scope Ref m) a)
    -- ^ Abstract extensible components of a closed expression
  | Open k m a `Update` Open k m a
  deriving (Functor, Foldable, Traversable)
  
reprOpen :: Open k (Repr k) a -> Repr k a
reprOpen o = let val = Val (o `App` val) o in val
  
hoistOpen :: (Ord k, Functor f) => (forall x. f x -> g x) -> Open k f a -> Open k g a
hoistOpen f (Open e) = Open (f e)
hoistOpen f (Defn d) = Defn (hoistClosed (hoistScope f) d)
hoistOpen f (o1 `Update` o2) = hoistOpen f o1 `Update` hoistOpen f o2
  
  
-- e.g. 
-- Defn (Open (Var (B Self)) `App` Scope (Var (B Self))) :: Open k a
-- Defn (Scope (Var (B Self)) `App` Scope (Var (B Self))) `App` Var a :: Closed k (Open k) a
-- Var a `App` Var a :: Closed k (Open k) a
  
-- | Closed expression with fixed set of nested values
data Closed k m a =
    Closed (m a)
  | Open k m a `App` m a
    -- ^ Application closes an open expression
  | Block (M.Map k (m a))
    -- ^ Set of public components
  | Closed k m a `Fix` k
  | Closed k m a `Concat` Closed k m a
  deriving (Functor, Foldable, Traversable)
  
reprClosed :: Ord k => Closed k (Repr k) a -> Repr k a
reprClosed c = Val c (Defn (hoistClosed lift c))

hoistClosed :: (Ord k, Functor f) => (forall x . f x -> g x) -> Closed k f a -> Closed k g a
hoistClosed f (Closed e) = Closed (f e)
hoistClosed f (o `App` e) = hoistOpen f o `App` f e
hoistClosed f (Block m) = Block (M.map f m)
hoistClosed f (c `Fix` x) = hoistClosed f c `Fix` x
hoistClosed f (c1 `Concat` c2) = hoistClosed f c1 `Concat` hoistClosed f c2
  
  
-- | Marker type for self- and super- references
data Ref = Super | Self deriving (Eq, Show)

ref :: a -> a -> Ref -> a
ref a _ Super = a
ref _ b Self = b
  
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
  
  Var a        >>= f = f a
  Val c o      >>= f = Val (c >>>= f) (o >>>= f)
  Let ds d     >>= f = Let (map (>>>= f) ds) (d >>>= f)
  Prim p       >>= f = Prim (fmap (>>= f) p)
  c `At` x     >>= f = (c >>>= f) `At` x
  c `AtPrim` t >>= f = (c >>>= f) `AtPrim` t

instance Bound (Open k) where
  Open e         >>>= f = Open (e >>= f)
  Defn d         >>>= f = Defn (d >>>= lift . f)
  o1 `Update` o2 >>>= f = (o1 >>>= f) `Update` (o2 >>>= f)
  
instance Bound (Closed k) where
  Closed e       >>>= f = Closed (e >>= f)
  o `App` e      >>>= f = (o >>>= f) `App` (e >>= f)
  Block m        >>>= f = Block (fmap (>>= f) m)
  c `Fix` x      >>>= f = (c >>>= f) `Fix` x
  c1 `Concat` c2 >>>= f = (c1 >>>= f) `Concat` (c2 >>>= f)
    
        
instance (Ord k, Eq a) => Eq (Repr k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Repr k) where
  liftEq eq = f where
    f (Var a)          (Var b)          = eq a b
    f (Val c1 o1)      (Val c2 o2)      = liftEq eq c1 c2 && liftEq eq o1 o2
    f (Let ds1 d1)     (Let ds2 d2)     = liftEq (liftEq eq) ds1 ds2 && liftEq eq d1 d2
    f (Prim p1)        (Prim p2)        = liftEq (liftEq eq) p1 p2
    f (c1 `At` x1)     (c2 `At` x2)     = liftEq eq c1 c2 && x1 == x2
    f (c1 `AtPrim` t1) (c2 `AtPrim` t2) = liftEq eq c1 c2 && t1 == t2
    f _                _                = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Open k m) where
  liftEq eq = f where
    f (Open e1)        (Open e2)        = liftEq eq e1 e2
    f (Defn d1)        (Defn d2)        = liftEq eq d1 d2
    f (o1 `Update` w1) (o2 `Update` w2) = liftEq eq o1 o2 && liftEq eq w1 w2
    f  _               _                = False
    
instance (Ord k, Eq1 m, Monad m) => Eq1 (Closed k m) where
  liftEq eq = f where
    f (Closed e1)      (Closed e2)      = liftEq eq e1 e2
    f (a1 `App` a2)    (b1 `App` b2)    = liftEq eq a1 b1 && liftEq eq a2 b2
    f (Block m1)       (Block m2)       = liftEq (liftEq eq) m1 m2
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
    Val c o      -> showsBinaryWith f' f' "Val" i c o
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

instance (Ord k, Show k, Show1 m) => Show1 (Open k m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Open k m a -> ShowS
  liftShowsPrec f g i e = case e of
    Open e       -> showsUnaryWith f' "Open" i e
    Defn d       -> showsUnaryWith f' "Defn" i d
    e `Update` w -> showsBinaryWith f' f' "Update" i e w
    where 
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      --g' :: forall f . Show1 f => [f a] -> ShowS
      --g' = liftShowList f g
      
      --f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      --f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k, Show1 m) => Show1 (Closed k m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Closed k m a -> ShowS
  liftShowsPrec f g i e = case e of 
    Closed e       -> showsUnaryWith f' "Closed" i e
    a1 `App` a2    -> showsBinaryWith f' f' "App" i a1 a2
    Block m        -> showsUnaryWith f'' "Block" i m
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
  c #. i = Closed c `At` Key i
  
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
  

    
