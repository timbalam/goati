{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}

-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..)
  , Ref(..), ref
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


-- | Runtime value representation 
data Repr k a =
    Var a
  | Let [Scope Int (Repr k) a] (Scope Int (Repr k) a)
    -- ^ Local recursive definitions
  | Block (M.Map k (Repr k a)) (M.Map k (Scope Ref (Repr k) a))
    -- ^ Set of public components with memo-ised current value
  | Prim (Prim (Repr k a))
    -- ^ Primitives
  | Call k (Repr k a) (Repr k a)
    -- ^ Field access with 'self' value
  | Repr k a `Update` Repr k a
    -- ^ Bind 'super' value
  | Repr k a `Fix` k
  deriving (Functor, Foldable, Traversable)
  
  
-- | Marker type for self- and super- references
data Ref = Super | Self deriving (Eq, Show)

ref :: a -> a -> Ref -> a
ref su _  Super = su
ref _  se Self  = se
  
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
  
  e >>= f = go e where
    go (Var a)          = f a
    go (Let en s)       = Let (map (>>>= f) en) (s >>>= f)
    go (Block c b)      = Block (fmap (>>= f) c) (fmap (>>>= f) b)
    go (Prim p)         = Prim (fmap (>>= f) p)
    go (Call x e1 e2)   = Call x (e1 >>= f) (e2 >>= f)
    go (e1 `Update` e2) = (e1 >>= f) `Update` (e2 >>= f)
    go (e `Fix` x)      = (e >>= f) `Fix` x
  

instance (Ord k, Eq a) => Eq (Repr k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Repr k) where
  liftEq eq = f where
    f (Var a)            (Var b)            = eq a b
    f (Let dsa da)       (Let dsb db)       = liftEq (liftEq eq) dsa dsb && liftEq eq da db
    f (Block _ ba)       (Block _ bb)       = liftEq (liftEq eq) ba bb
    f (Prim pa)          (Prim pb)          = liftEq (liftEq eq) pa pb
    f (Call xa e1a e2a)  (Call xb e1b e2b)  = liftEq eq e1a e1b && liftEq eq e2a e2b && xa == xb
    f (e1a `Update` e2a) (e1b `Update` e2b) = liftEq eq e1a e1b && liftEq eq e2a e2b
    f (ea `Fix` xa)      (eb `Fix` xb)      = liftEq eq ea eb && xa == xb
    f  _                 _                  = False
    
    
instance (Ord k, Show k, Show a) => Show (Repr k a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Repr k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Repr k a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a          -> showsUnaryWith f "Var" i a
    Let d ds       -> showsBinaryWith f'' f' "Let" i d ds
    Block _ b      -> showsUnaryWith f'' "block" i b
    Prim p         -> showsUnaryWith f'' "Prim" i p
    Call k e1 e2   -> showsTrinaryWith showsPrec f' f' "Call" i k e1 e2 
    e1 `Update` e2 -> showsBinaryWith f' f' "Update" i e1 e2
    e `Fix` k      -> showsBinaryWith f' showsPrec "Fix" i e k
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
      
instance S.Self a => S.Self (Repr k a) where
  self_ = Var . S.self_
  
instance S.Local a => S.Local (Repr k a) where
  local_ = Var . S.local_
  
instance S.Field (Repr (Tag k) a) where
  type Compound (Repr (Tag k) a) = Repr (Tag k) a
  e #. i = Call (Key i) e e
  
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
    Binop op e w -> showsTrinaryWith showsPrec f f "Binop" i op e w
    
    
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
  

-- Utility function
showsTrinaryWith sp1 sp2 sp3 n i a1 a2 a3 = showParen (i > 10)
      (showString n . sp1 11 a1 . showChar ' ' . sp2 11 a2
        . showChar ' ' . sp3 11 a3)
    
