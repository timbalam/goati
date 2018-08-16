{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}

-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..), Defns(..), Ref(..)
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
import Bound.Scope (hoistScope)


-- | Runtime value representation using chain of 'super' values
newtype Repr k a = Repr { getRepr :: [Defns k a] }
  deriving (Functor, Foldable, Traversable)

data Defns k a =
    Var a
  | Let [Scope Int (Repr k) a] (Scope Int (Repr k) a)
    -- ^ Local recursive definitions
  | Block (M.Map k (Cache (Repr k) a))
    -- ^ Set of public components
  | Prim (Prim (Repr k a))
    -- ^ Primitives
  | Repr k a `At` k
  | Repr k a `AtPrim` IOPrimTag (Repr k Void)
  | Repr k a `Fix` k
  | Defns k a `App` Repr k a
    -- ^ Bind 'self' value
  deriving (Functor, Foldable, Traversable)
  
  
-- | An extensible value with memoised current value
data Cache m a = Cache (m a) (Scope Ref m a)
  deriving (Functor, Foldable, Traversable)
  
  
-- | Marker type for self- and super- references
data Ref = Super | Self deriving (Eq, Show)
  
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
  pure = Repr . pure . Var
  (<*>) = ap
  
instance Ord k => Monad (Repr k) where
  return = pure
  
  Repr es >>= f = Repr (es >>= go) where
    go (Var a)        = getRepr (f a)
    go (Let en x)     = pure (Let (map (>>>= f) en) (x >>>= f))
    go (Block b)      = (pure . Block) (fmap (>>>= f) b)
    go (Prim p)       = (pure . Prim) (fmap (>>= f) p)
    go (e `At` x)     = pure ((e >>= f) `At` x)
    go (e `AtPrim` t) = pure ((e >>= f) `AtPrim` t)
    go (e `Fix` x)    = pure ((e >>= f) `Fix` x)
    go (d `App` e)    = map (`App` (e >>= f)) (go d)
    
instance Bound Cache where
  Cache e s >>>= f = Cache (e >>= f) (s >>>= f)
  

instance (Ord k, Eq a) => Eq (Defns k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Defns k) where
  liftEq eq = f where
    f (Var a)            (Var b)            = eq a b
    f (Let dsa da)       (Let dsb db)       = liftEq (liftEq eq) dsa dsb && liftEq eq da db
    f (Block ba)         (Block bb)         = liftEq (liftEq eq) ba bb
    f (Prim pa)          (Prim pb)          = liftEq (liftEq eq) pa pb
    f (ea `At` xa)       (eb `At` xb)       = liftEq eq ea eb && xa == xb
    f (ea `AtPrim` ta)   (eb `AtPrim` tb)   = liftEq eq ea eb && ta == tb
    f (ea `Fix` xa)      (eb `Fix` xb)      = liftEq eq ea eb && xa == xb
    f (e1a `App` e2a)    (e1b `App` e2b)    = liftEq eq e1a e1b && liftEq eq e2a e2b
    f  _                 _                  = False
    
instance Ord k => Eq1 (Repr k) where
  liftEq eq (Repr es1) (Repr es2) = liftEq (liftEq eq) es1 es2
    
instance (Eq1 m, Monad m) => Eq1 (Cache m) where
  liftEq eq (Cache _ sa) (Cache _ sb) = liftEq eq sa sb
    
    
instance (Ord k, Show k, Show a) => Show (Defns k a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Defns k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Defns k a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a          -> showsUnaryWith f "Var" i a
    Let d ds       -> showsBinaryWith f'' f' "Let" i d ds
    Block b        -> showsUnaryWith f'' "Block" i b
    Prim p         -> showsUnaryWith f'' "Prim" i p
    e `At` k       -> showsBinaryWith f' showsPrec "At" i e k 
    e `AtPrim` p   -> showsBinaryWith f' showsPrec "AtPrim" i e p
    e `Fix` k      -> showsBinaryWith f' showsPrec "Fix" i e k
    e1 `App` e2    -> showsBinaryWith f' f' "App" i e1 e2
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k) => Show1 (Repr k) where
  liftShowsPrec f g i (Repr es) = showsUnaryWith f'' "Repr" i es
    where
      f' = liftShowsPrec f g
      g' = liftShowList f g
      f'' = liftShowsPrec f' g'
      
instance (Show1 m, Monad m) => Show1 (Cache m) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Cache m a -> ShowS
  liftShowsPrec f g i (Cache m s) = showsBinaryWith f' f' "Cache" i m s
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      
instance S.Self a => S.Self (Repr k a) where
  self_ = Repr . pure . Var . S.self_
  
instance S.Local a => S.Local (Repr k a) where
  local_ = Repr . pure . Var . S.local_
  
instance S.Field (Repr (Tag k) a) where
  type Compound (Repr (Tag k) a) = Repr (Tag k) a
  e #. i = (Repr . pure) (e `At` Key i)
  
nume = error "Num (Repr k a)"

instance Num (Repr k a) where
  fromInteger = Repr . pure . Prim . Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Fractional (Repr k a)"

instance Fractional (Repr k a) where
  fromRational = Repr . pure . Prim . Number . fromRational
  (/) = frace
  
instance IsString (Repr k a) where
  fromString = Repr . pure . Prim . Text . fromString

instance S.Lit (Repr k a) where
  unop_ op = Repr . pure . Prim . Unop op
  binop_ op a b = (Repr . pure . Prim) (Binop op a b)
      
      
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
  

    
