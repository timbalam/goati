{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies, PolyKinds, StandaloneDeriving, FlexibleContexts, TypeOperators #-}

-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..), Open(..), Closed(..)
  --, Ref(..), ref
  , Prim(..)
  , IOPrimTag(..)
  , Tag(..)
  , Nec(..), nec
  , S.Ident, S.Unop(..), S.Binop(..)
  , Var(..), Bound(..), Scope(..)
  )
  where
  

import qualified My.Types.Syntax.Class as S
import qualified Control.Category as C (Category(..))
import Control.Monad (ap)
import Control.Monad.Trans
import Control.Monad.Trans.Identity (IdentityT(..))
import Control.Exception (IOException)
import Data.Functor.Classes
import Data.IORef (IORef)
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Set as S
import Data.String (IsString(..))
import qualified Data.Text as T
import Data.Traversable (foldMapDefault, fmapDefault)
import System.IO (Handle, IOMode)
import Bound


-- | Runtime value representation 
data Repr k v a = 
    Var a
  | Val (v a) (Open k (Repr k v) a)
  | Let [Scope Int (Repr k v) a] (Scope Int (Repr k v) a)
    -- ^ Local recursive definitions
  | Prim (Prim (Repr k v a))
    -- ^ Primitives
  | Closed k IdentityT IdentityT (Repr k v) a `At` k
    -- ^ Field access with 'self' value
  deriving (Functor, Foldable, Traversable)
  
update :: Measure v (Open k (Repr v k)) => Repr v k m a -> Repr v k m a -> Repr v k m a
update e1 e2 = Self (Super (e1' `Update` d2)) where
  e1' = Self (fmap (F . Var) e1 `App` lift (Var (B ())))
  
  d1 = toSelf (Open e1)
  d2 = toSelf (Open e2)
  
  

  
data Closed k se su m a =
    Closed (se (su m) a)
  | Block (M.Map k (se (su m) a))
    -- ^ Set of public components
  | se (su m) a `Update` Defns k se m a
    -- ^ Bind 'super' value
  | Closed k se su m a `Fix` k
  | Closed k se su m a `Concat` Closed k se su m a
  deriving (Functor, Foldable, Traversable)
  

data Open k m a =
    Open (m a)
  | Self (Defns k (Scope ()) m a)
  deriving (Functor, Foldable, Traversable)
  
toSelf :: Monad m => Open k m a -> Defns k (Scope ()) m a
toSelf o = o `App` (Scope . return . B) ()
  
data Defns k se m a =
    Super (Closed k se (Scope ()) m a)
  | Open k m a `App` se m a
    -- ^ Bind 'self' value
    
toSuper :: Measure v (Open k (Repr v k) a) => Defns k (Scope ()) (Repr v k) a -> Closed k (Scope ()) (Scope ()) (Repr v k) a
toSuper d = par `Update` d where
  par =
    (Scope . Scope . val . Self) ((Open . Var . F . Var . B) () `App` (return . B) ())
  
  
deriving instance Functor m => Functor (Defns k IdentityT m)
deriving instance Functor m => Functor (Defns k (Scope ()) m)
deriving instance Foldable m => Foldable (Defns k IdentityT m)
deriving instance Foldable m => Foldable (Defns k (Scope ()) m)
deriving instance Traversable m => Traversable (Defns k IdentityT m)
deriving instance Traversable m => Traversable (Defns k (Scope ()) m)
  
instance Ord k => Bound (Open k) where
  Open e >>>= f = Open (e >>= f)
  Self d >>>= f = Self (d >>>= f)
  
instance (Ord k, Bound t) => Bound (Defns k t) where
  Super c   >>>= f = Super (c >>>= f)
  o `App` e >>>= f = (o >>>= f) `App` (e >>>= f)
  
instance (Ord k, Bound s, Bound t) => Bound (Closed k s t) where
  Closed e       >>>= f = (Closed . getT_) (T_ e >>>= f)
  Block b        >>>= f = Block (fmap (get_T . (>>>= f) . T_) b)
  e `Update` d   >>>= f = (e >>>= f) `Update` (d >>>= f)
  c1 `Concat` c2 >>>= f = (c1 >>>= f) `Concat` (c2 >>>= f)
  c `Fix` x      >>>= f = (c >>>= f) `Fix` x
  
  
-- | Marker type for self- and super- references
--data Ref = Super | Self deriving (Eq, Show)

--ref :: a -> a -> Ref -> a
--ref su _  Super = su
--ref _  se Self  = se
  
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
  
  Var a     >>= f = f a
  Val c o   >>= f = Val (c >>>= f) (o >>>= f)
  Let en s  >>= f = Let (map (>>>= f) en) (s >>>= f)
  Prim p    >>= f = Prim (fmap (>>= f) p)
  c `At` x  >>= f = (c >>>= f) `At` x
  

instance (Ord k, Eq a) => Eq (Repr k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Repr k) where
  liftEq eq (Var a)      (Var b)       = eq a b
  liftEq eq (Val _ oa)   (Val _ ob)    = liftEq eq oa ob
  liftEq eq (Let ena sa) (Let enb sb)  = liftEq (liftEq eq) ena enb && liftEq eq sa sb
  liftEq eq (Prim pa)    (Prim pb)     = liftEq (liftEq eq) pa pb
  liftEq eq (ca `At` x)  (cb `At` x')  = liftEq eq ca cb && x == x'
  liftEq _  _            _             = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Open k m) where
  liftEq eq (Open ea) (Open eb) = liftEq eq ea eb
  liftEq eq (Self da) (Self db) = liftEq eq da db
  liftEq _  _         _         = False
  
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Defns k IdentityT m) where liftEq = liftEqDefns
instance (Ord k, Eq1 m, Monad m) => Eq1 (Defns k (Scope ()) m) where liftEq = liftEqDefns

liftEqDefns
  :: (Ord k, Eq1 m, Monad m, Eq1 (t m), Eq1 (T t (Scope ()) m))
  => (a -> b -> Bool) -> Defns k t m a -> Defns k t m b -> Bool
liftEqDefns eq (Super ca)    (Super cb)    = liftEq eq ca cb
liftEqDefns eq (oa `App` ea) (ob `App` eb) = liftEq eq oa ob && liftEq eq ea eb
liftEqDefns _  _             _             = False
  
instance (Ord k, Eq1 m, Monad m, Eq1 (t m)) => Eq1 (Closed k t m) where
  liftEq eq (Closed ea)        (Closed eb)        = liftEq eq ea eb
  liftEq eq (Block ba)         (Block bb)         = liftEq (liftEq eq) ba bb
  liftEq eq (ea `Update` da)   (eb `Update` db)   = liftEq eq ea eb && liftEq eq da db
  liftEq eq (c1a `Concat` c2a) (c1b `Concat` c2b) = liftEq eq c1a c1b && liftEq eq c2a c2b
  liftEq eq (ca `Fix` x)       (cb `Fix` x')      = liftEq eq ca cb && x == x'
  liftEq _  _                  _                  = False
    
    
instance (Ord k, Show k, Show a) => Show (Repr k a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Repr k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Repr k a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a     -> showsUnaryWith f "Var" i a
    Val _ b   -> showsUnaryWith f' "val" i b
    Let d ds  -> showsBinaryWith f'' f' "Let" i d ds
    Prim p    -> showsUnaryWith f'' "Prim" i p
    c `At` x  -> showsBinaryWith f' showsPrec "At" i c x
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
  
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Open k m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Open k m a -> ShowS
  liftShowsPrec f g i e = case e of
    Open e -> showsUnaryWith f' "Open" i e
    Self d -> showsUnaryWith f' "Self" i d
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Defns k IdentityT m) where
  liftShowsPrec = liftShowDefns
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Defns k (Scope ()) m) where
  liftShowsPrec = liftShowDefns

liftShowDefns
  :: forall k m t a. (Ord k, Show k, Show1 m, Monad m, Show1 (t m), Show1 (T t (Scope ()) m))
  => (Int -> a -> ShowS) -> ([a] -> ShowS)
  -> Int -> Defns k t m a -> ShowS
liftShowDefns f g i e = case e of
  Super e   -> showsUnaryWith f' "Super" i e
  o `App` e -> showsBinaryWith f' f' "App" i o e
  where
    f' :: forall f. Show1 f => Int -> f a -> ShowS
    f' = liftShowsPrec f g
      
      
instance (Ord k, Show k, Show1 m, Show1 (t m), Monad m) => Show1 (Closed k t m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Closed k t m a -> ShowS
  liftShowsPrec f g i e = case e of
    Closed e       -> showsUnaryWith f' "Closed" i e
    Block b        -> showsUnaryWith f'' "Block" i b
    e `Update` d   -> showsBinaryWith f' f' "Update" i e d
    c1 `Concat` c2 -> showsBinaryWith f' f' "Concat" i c1 c2
    c `Fix` x      -> showsBinaryWith f' showsPrec "Fix" i c x
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
  e #. i = Closed (IdentityT e) `At` Key i
  
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
  

-- Utility code
showsTrinaryWith sp1 sp2 sp3 n i a1 a2 a3 = showParen (i > 10)
      (showString n . sp1 11 a1 . showChar ' ' . sp2 11 a2
        . showChar ' ' . sp3 11 a3)
    

newtype T
  (s :: (k -> *) -> k -> *)
  (t :: (k -> *) -> k -> *)
  (m :: (k -> *))
  (a :: k) = T_ { getT_ :: s (t m) a }
  deriving (Functor, Foldable, Traversable)
    
instance Bound s => Bound (T s (Scope ())) where
  T_ b >>>= f = T_ (b >>>= lift . f)
  
instance (Eq1 m, Monad m) => Eq1 (T IdentityT (Scope ()) m) where liftEq = liftEqT
instance (Eq1 m, Monad m) => Eq1 (T (Scope ()) (Scope ()) m) where liftEq = liftEqT
  
liftEqT
  :: Eq1 (s (t m)) => (a -> b -> Bool) -> T s t m a -> T s t m b -> Bool
liftEqT eq (T_ sa) (T_ sb) = liftEq eq sa sb
  
instance Show1 m => Show1 (T IdentityT (Scope ()) m) where liftShowsPrec = liftShowT
instance Show1 m => Show1 (T (Scope ()) (Scope ()) m) where liftShowsPrec = liftShowT
  
liftShowT
  :: Show1 (s (t m)) => (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> T s t m a -> ShowS
liftShowT f g i (T_ s) = showsUnaryWith (liftShowsPrec f g) "T_" i s
