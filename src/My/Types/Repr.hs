{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}
--{#- LANGUAGE UndecidableInstances #-}


-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..)
  , Prim(..)
  , IOPrimTag(..)
  , Defns(..)
  , Rec(..), toRec, abstractRec
  , Tag(..)
  , BuiltinSymbol(..)
  , S.Ident, S.Unop(..), S.Binop(..)
  , Var(..), Bound(..), Scope(..)
  )
  where
  

import qualified My.Types.Syntax.Class as S
import Control.Monad (ap)
import Control.Monad.Trans
import Control.Exception (IOException)
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
import Bound.Scope (mapBound, abstractEither)



-- | Representation for a single expression layer
data ReprF k m a =
    Prim (Prim (m a))
  | Var a
  | Block (Defns k m a)
  | m a `At` k
  | m a `Fix` k
  | m a `AtPrim` (IOPrimTag (m Void))
  deriving (Functor, Foldable, Traversable)
  

-- | A non-empty chain of value updates
newtype Repr k a = Repr { getRepr :: [ReprF k (Repr k) a] }
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
  
  
-- | Set of recursive, extensible definitions / parameter bindings
data Defns k m a =
  Defns
    [Rec k m a]
    -- ^ List of local defintions
    (M.Map k (Rec k m a))
    -- ^ Publicly visible definitions
  deriving (Functor, Foldable, Traversable)
  
  
-- | Wraps bindings for a triple of scopes as contained by 'Defns'.
-- From outer to inner, the scopes represent
--    * indices into the list of private local definitions
--    * self bound variables
newtype Rec k m a = Rec { getRec :: Scope (Either Int k) (Scope k m) a }
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  

-- | Construct a 'Rec' from a classic de Bruijn representation
toRec :: Monad m => m (Var k (Var Int a)) -> Rec k m a
toRec = Rec . mapBound Left . toScope . toScope
  
  
-- | Abstract an expression into a 'Rec'
abstractRec
  :: Monad m
  => (b -> Either Int c)
  -- ^ abstract public bound variables
  -> (a -> Either k b)
  -- ^ abstract self bound variables
  -> m a
  -- ^ Expression
  -> Rec k m c
  -- ^ Expression with bound variables
abstractRec f g = Rec . mapBound Left . abstractEither f . abstractEither g



foldMapRec
  :: (Foldable f, Monoid r)
  => (k -> r)
  -> (Either Int k -> r)
  -> (a -> r)
  -> Rec k f a
  -> r
foldMapRec f g h (Rec (Scope m)) = foldMapScope f (bifoldMap g (foldMapScope f h))
    
    
-- | Repression key type
data Tag k =
    Key S.Ident
  | Symbol k
  | Builtin BuiltinSymbol
  deriving (Eq, Show)
  
  
data BuiltinSymbol =
    Self
  | SkipAsync
  deriving (Eq, Ord, Show)

  
instance Ord k => Applicative (Repr k) where
  pure = return
  
  (<*>) = ap
  
instance Ord k => Monad (Repr k) where
  return = Repr . pure . Var
  
  Repr vs >>= f = Repr (vs >>= bindF) where
    bindF (Prim p) = (pure . Prim) ((>>= f) <$> p)
    bindF (Var a) = getRepr (f a)
    bindF (Block b) = (pure . Block) (b >>>= f)
    bindF (e `At` x) = pure ((e >>= f) `At` x)
    bindF (e `Fix` x) = pure ((e >>= f) `Fix` x)
    bindF (e `AtPrim` p) = pure ((e >>= f) `AtPrim` p)
    
  
instance (Ord k, Eq a) => Eq (Repr k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Repr k) where
  liftEq eq (Repr vas) (Repr vbs) = liftEq (liftEq eq) vas vbs
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (ReprF k m) where
  liftEq eq = f where
    f (Prim pa)        (Prim pb)        = liftEq (liftEq eq) pa pb
    f (Var a)          (Var b)          = eq a b
    f (Block ba)       (Block bb)       = liftEq eq ba bb
    f (ea `At` xa)     (eb `At` xb)     = liftEq eq ea eb && xa == xb
    f (ea `Fix` xa)    (eb `Fix` xb)    = liftEq eq ea eb && xa == xb
    f (ea `AtPrim` pa) (eb `AtPrim` pb) = liftEq eq ea eb && pa == pb
    f  _                   _            = False
   
   
instance (Ord k, Show k, Show a) => Show (Repr k a) where
  showsPrec = showsPrec1

instance (Ord k, Show k) => Show1 (Repr k) where
  liftShowsPrec f g i (Repr vs) = showsUnaryWith f'' "Repr" i vs
    where
      f' = liftShowsPrec f g
      g' = liftShowList f g
      f'' = liftShowsPrec f' g'

instance (Ord k, Show k, Show1 m, Monad m) => Show1 (ReprF k m) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> ReprF k m a -> ShowS
  liftShowsPrec f g i e = case e of
    Prim p       -> showsUnaryWith f'' "Prim" i p  
    Var a        -> showsUnaryWith f "Var" i a
    Block d      -> showsUnaryWith f' "Block" i d
    e `At` k     -> showsBinaryWith f' showsPrec "At" i e k
    e `Fix` k    -> showsBinaryWith f' showsPrec "Fix" i e k
    e `AtPrim` p -> showsBinaryWith f' showsPrec "AtPrim" i e p
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f. Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
      g'' :: forall f g. (Show1 f, Show1 g) => [f (g a)] -> ShowS
      g'' = liftShowList f' g'
      
      f''' :: forall f g h. (Show1 f, Show1 g, Show1 h) => Int -> f (g (h a)) -> ShowS
      f''' = liftShowsPrec f'' g''
      
      
instance S.Self a => S.Self (Repr k a) where
  self_ = Repr . pure . Var . S.self_
  
instance S.Self a => S.Self (ReprF k m a) where
  self_ = Var . S.self_
  
instance S.Local a => S.Local (Repr k a) where
  local_ = Repr . pure . Var . S.local_
  
instance S.Local a => S.Local (ReprF k m a) where
  local_ = Var . S.local_
  
instance S.Field (Repr (Tag k) a) where
  type Compound (Repr (Tag k) a) = Repr (Tag k) a
  
  e #. i = (Repr . pure) (e `At` Key i)
  
instance S.Field (ReprF (Tag k) m a) where
  type Compound (ReprF (Tag k) m a) = m a
  
  e #. i = e `At` Key i

  
instance Num (Repr k a) where
  fromInteger = Repr . pure . fromInteger
  (+) = error "Num (Repr k a)"
  (-) = error "Num (Repr k a)"
  (*) = error "Num (Repr k a)"
  abs = error "Num (Repr k a)"
  signum = error "Num (Repr k a)"
  negate = error "Num (Repr k a)"
  
instance Num (ReprF k m a) where
  fromInteger = Prim . Number . fromInteger
  (+) = error "Num (Repr k a)"
  (-) = error "Num (Repr k a)"
  (*) = error "Num (Repr k a)"
  abs = error "Num (Repr k a)"
  signum = error "Num (Repr k a)"
  negate = error "Num (Repr k a)"
  
instance Fractional (Repr k a) where
  fromRational = Repr . pure . fromRational
  (/) = error "Num (Repr k a)"
  
instance Fractional (ReprF k m a) where
  fromRational = Prim . Number . fromRational
  (/) = error "Num (Repr k a)"
  
instance IsString (Repr k a) where
  fromString = Repr . pure . fromString
  
instance IsString (ReprF k m a) where
  fromString = Prim . Text . fromString
  
instance S.Lit (Repr k a) where
  unop_ op = Repr . pure . Prim . Unop op
  binop_ op a b = (Repr . pure . Prim) (Binop op a  b)
      
      
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
       
        
instance Ord k => Bound (Defns k) where
  Defns en se >>>= f = Defns ((>>>= f) <$> en) ((>>>= f) <$> se)

instance (Ord k, Eq1 m, Monad m) => Eq1 (Defns k m) where
  liftEq
    :: forall a b. (a -> b -> Bool)
    -> Defns k m a -> Defns k m b  -> Bool
  liftEq eq (Defns ena sea) (Defns enb seb) =
    liftEq f ena enb && liftEq f sea seb
    where
      f :: forall f . Eq1 f => f a -> f b -> Bool
      f = liftEq eq
        
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Defns k m) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Defns k m a -> ShowS
  liftShowsPrec f g i (Defns en se) =
    showsBinaryWith f'' f'' "Defns" i en se
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
  

    
