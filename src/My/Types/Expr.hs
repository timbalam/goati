{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies #-}
--{#- LANGUAGE UndecidableInstances #-}


-- | Module of my language core expression data types
module My.Types.Expr
  ( Expr
  , expr, runExpr
  , ExprT(..)
  , ExprF(..)
  , prim, block, var, update, at, fix, atPrim
  , Prim(..)
  , IOPrimTag(..)
  , Defns(..)
  , Node(..)
  , Rec(..), toRec, foldMapBoundRec, abstractRec
  , Tag(..)
  , BuiltinSymbol(..)
  , S.Ident, S.Unop(..), S.Binop(..)
  , Var(..), Bound(..), Scope(..)
  , Nec(..), NecType(..)
  )
  where
  

--import My.Types.Parser (Ident, Key(..), Unop(..), Binop(..))
import qualified My.Types.Syntax.Class as S
import My.Util ((<&>), Susp(..))
import Control.Monad (ap)
import Control.Monad.Trans
import Control.Monad.Free (Free(..))
import Control.Exception (IOException)
import Data.Functor.Classes
import Data.Functor.Identity (Identity(..))
import Data.Void
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Data.IORef (IORef)
import Data.String (IsString(..))
import Text.Show (showListWith)
import System.IO (Handle, IOMode)
import Bound
import Bound.Scope (foldMapScope, foldMapBound, abstractEither)


type Expr k = ExprT k Identity

runExpr :: Expr k a -> ExprF k (Expr k) a
runExpr = runIdentity . runExprT

expr :: Monad m => ExprF k (ExprT k m) a -> ExprT k m a
expr = ExprT . return

-- | Interpreted my language expression
data ExprF k m a =
    Prim (Prim (m a))
  | Var a
  | Block (Defns k m a)
  | m a `Update` Defns k m a
  | m a `At` k
  | m a `Fix` k
  | m a `AtPrim` (IOPrimTag (m Void))
  deriving (Functor, Foldable, Traversable)
  
newtype ExprT k m a = ExprT { runExprT :: m (ExprF k (ExprT k m) a) }
  deriving (Functor, Foldable, Traversable)
  
prim :: Monad m => Prim (ExprT k m a) -> ExprT k m a
prim = expr . Prim

var :: Monad m => a -> ExprT k m a
var = expr . Var

block :: Monad m => Defns k (ExprT k m) a -> ExprT k m a
block = expr . Block

update :: Monad m => ExprT k m a -> Defns k (ExprT k m) a -> ExprT k m a
update e b = expr (e `Update` b)

at :: Monad m => ExprT k m a -> k -> ExprT k m a
at e k = expr (e `At` k)

fix :: Monad m => ExprT k m a -> k -> ExprT k m a
fix e k = expr (e `Fix` k)

atPrim :: Monad m => ExprT k m a -> IOPrimTag (ExprT k m Void) -> ExprT k m a
atPrim e p = expr (e `AtPrim` p)
  
  
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
  

-- | Set of extensible field bindings that can be recursive parameter sets
data Defns k m a =
    Defns
      (S.Set RecType)
      [(S.Ident, Rec k m a)]
      -- ^ List of local defintions
      (M.Map k (Node k (Rec k m a)))
      -- ^ Publicly visible definitions
  | Fields
      (M.Map k (Node k (m a)))
  deriving (Functor, Foldable, Traversable)
  
data RecType = Browse
  deriving (Eq, Show)
  
  
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
    Key S.Ident
  | Symbol k
  | Builtin BuiltinSymbol
  deriving (Eq, Show)
  
  
data BuiltinSymbol =
    SelfS
  | SkipAsyncS
  deriving (Eq, Ord, Show)

  
instance (Ord k, Monad m) => Applicative (ExprT k m) where
  pure = return
  
  (<*>) = ap
  
instance (Ord k, Monad m) => Monad (ExprT k m) where
  return = var
  
  ExprT m >>= f = ExprT (m >>= runExprT . bindT) where
    bindT e = case e of
      Prim p        -> prim ((>>= f) <$> p)
      Var a         -> f a
      Block b       -> block (b >>>= f)
      e `Update` b  -> (e >>= f) `update` (b >>>= f)
      e `At` x      -> (e >>= f) `at` x
      e `Fix` m     -> (e >>= f) `fix` m
      e `AtPrim` p  -> (e >>= f) `atPrim` p
  
instance (Ord k, Eq1 m, Monad m, Eq a) => Eq (ExprT k m a) where
  (==) = eq1
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (ExprF k m) where
  liftEq eq (Prim pa)        (Prim pb)        = liftEq (liftEq eq) pa pb
  liftEq eq (Var a)          (Var b)          = eq a b
  liftEq eq (Block ba)       (Block bb)       = liftEq eq ba bb
  liftEq eq (ea `Update` ba) (eb `Update` bb) = liftEq eq ea eb && liftEq eq ba bb
  liftEq eq (ea `At` xa)     (eb `At` xb)     = liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)    (eb `Fix` xb)    = liftEq eq ea eb && xa == xb
  liftEq eq (ea `AtPrim` pa) (eb `AtPrim` pb) = liftEq eq ea eb && pa == pb
  liftEq eq _                _                = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (ExprT k m) where
  liftEq eq (ExprT ma) (ExprT mb) = liftEq (liftEq eq) ma mb
   
instance (Ord k, Show k, Show1 m, Monad m, Show a) => Show (ExprT k m a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (ExprF k m) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> ExprF k m a -> ShowS
  liftShowsPrec f g i e = case e of
    Prim p       -> showsUnaryWith f'' "Prim" i p  
    Var a        -> showsUnaryWith f "Var" i a
    Block d      -> showsUnaryWith f' "Block" i d
    e `Update` d -> showsBinaryWith f' f' "Update" i e d
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

instance (Ord k, Show k, Show1 m, Monad m) => Show1 (ExprT k m) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> ExprT k m a -> ShowS
  liftShowsPrec f g i (ExprT m) = showsUnaryWith f'' "Expr" i m 
    where 
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f. Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance S.Self a => S.Self (ExprF k m a) where
  self_ = Var . S.self_
  
instance (S.Self a, Monad m) => S.Self (ExprT k m a) where
  self_ = var . S.self_
  
instance S.Local a => S.Local (ExprF k m a) where
  local_ = Var . S.local_ 
  
instance (S.Local a, Monad m) => S.Local (ExprT k m a) where
  local_ = var . S.local_
  
instance S.Field (ExprF (Tag k) m a) where
  type Compound (ExprF (Tag k) m a) = m a
  
  m #. i = m `At` Key i
  
instance Monad m => S.Field (ExprT (Tag k) m a) where
  type Compound (ExprT (Tag k) m a) = ExprT (Tag k) m a

  e #. i = e `at` Key i

instance Num (ExprF k m a) where
  fromInteger = Prim . Number . fromInteger
  (+) = error "Num (ExprF k m a)"
  (-) = error "Num (ExprF k m a)"
  (*) = error "Num (ExprF k m a)"
  abs = error "Num (ExprF k m a)"
  signum = error "Num (ExprF k m a)"
  negate = error "Num (ExprF k m a)"
  
instance Monad m => Num (ExprT k m a) where
  fromInteger = prim . Number . fromInteger
  (+) = error "Num (ExprT k m a)"
  (-) = error "Num (ExprT k m a)"
  (*) = error "Num (ExprT k m a)"
  abs = error "Num (ExprT k m a)"
  signum = error "Num (ExprT k m a)"
  negate = error "Num (ExprT k m a)"
  
instance Fractional (ExprF k m a) where
  fromRational = Prim . Number . fromRational
  (/) = error "Num (ExprF k a)"
  
instance Monad m => Fractional (ExprT k m a) where
  fromRational = prim . Number . fromRational
  (/) = error "Num (ExprT k a)"
  
instance IsString (ExprF k m a) where
  fromString = Prim . Text . fromString
  
instance Monad m => IsString (ExprT k m a) where
  fromString = prim . Text . fromString
  
instance Monad m => S.Lit (ExprT k m a) where
  unop_ op = prim . Unop op
  binop_ op a b = prim (Binop op a b)
      
      
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
  x >>>= f = go x
    where
      go (Defns fl en se) =
        Defns fl (fmap (>>>= f) <$> en) (fmap (>>>= f) <$> se)
      go (Fields se) =
        Fields (fmap (>>= f) <$> se)
  
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Defns k m) where
  liftEq eq = cmp 
    where
      cmp (Defns fla ena sea) (Defns flb enb seb) =
        fla == flb && liftEq (le' eq) ena enb && liftEq (le' eq) sea seb
      cmp (Fields sea)         (Fields seb) =
        liftEq (le' eq) sea seb
      cmp  _                    _            = False
      
      le' :: (Eq1 f, Eq1 g) => (a -> b -> Bool) -> f (g a) -> f (g b) -> Bool
      le' eq = liftEq (liftEq eq)
        
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Defns k m) where
  liftShowsPrec
    :: forall a . (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Defns k m a -> ShowS
  liftShowsPrec f g i = go
    where
      go (Defns fl en se) = showParen (i > 11)
        (showString "Defns " . showsPrec 11 fl . showChar ' '
          . f''' 11 en . showChar ' ' . f''' 11 se)
      go (Fields se) = showsUnaryWith f''' "Fields" i se
      
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f. Show1 f => [f a] -> ShowS
      g' = liftShowList f g 
      
      f'' :: forall f g. (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
      g'' :: forall f g. (Show1 f, Show1 g) => [f (g a)] -> ShowS
      g'' = liftShowList f' g'
      
      f''' :: forall f g h. (Show1 f, Show1 g, Show1 h) => Int -> f (g (h a)) -> ShowS
      f''' = liftShowsPrec f'' g''
      
        
instance (Eq k, Eq a) => Eq (Node k a) where
  (==) = eq1
        
instance Eq k => Eq1 (Node k) where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open fa)  (Open fb) = liftEq (liftEq eq) fa fb

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
  

    
