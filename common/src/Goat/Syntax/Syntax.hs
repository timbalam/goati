{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, TypeFamilies #-}

-- | This module provides a mostly-depreciated set of concrete types for representing Goat syntax.
-- The types in this module are replaced by the typeclass encoding of the Goat syntax from Goat.Types.Syntax.Class.
-- However, they have been given implementations of the syntax classes and are a useful concrete representation for testing parsers.
module Goat.Syntax.Syntax
  ( Expr(..)
  , Group(..)
  , RecStmt(..)
  , Stmt(..)
  , S.Unop(..)
  , S.Binop(..)
  , Field(..)
  , Patt(..)
  , Program(..)
  , S.Ident(..)
  , Key(..)
  , StringExpr
  , Path
  , Import(..)
  , Vis(..), vis
  , Res(..)
  , Name
  , VarPath
  , Free(..)
  , S.prec
  ) where
import Control.Monad.Free
import Control.Applicative (liftA2)
import Control.Monad (ap)
import qualified Data.Text as T
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Typeable
import Data.List.NonEmpty (NonEmpty)
import Data.String (IsString(..))
import Data.Semigroup (Semigroup(..))
import Goat.Util
import qualified Goat.Syntax.Class as S
  
  
-- | Alias for typical variable name type
type Name a b = Res (Vis a b)


-- | Alias for typical set target type
type VarPath = Vis (Path S.Ident) (Path Key)


-- | Component name
newtype Key = K_ S.Ident
  deriving (Eq, Ord, Show, Typeable)
  
instance S.Self Key where
  self_ = K_
  

-- | External name
newtype Import = Use S.Ident
  deriving (Eq, Ord, Show, Typeable)
  
instance S.Extern Import where
  use_ = Use
 
 
-- | A path expression for my language recursively describes a set of nested
--   fields relative to a self- or environment-defined field
type Path = Free Field

data Field a = a `At` Key
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Field (Free Field a) where
  type Compound (Free Field a) = Free Field a
  p #. i = Free (p `At` K_ i)

instance S.Local a => S.Local (Free Field a) where
  local_ = Pure . S.local_
  
instance S.Self a => S.Self (Free Field a) where
  self_ = Pure . S.self_

-- | Binder visibility can be public or private to a scope
data Vis a b = Priv a | Pub b
  deriving (Eq, Ord, Show, Typeable, Functor, Foldable, Traversable)
  
vis :: (a -> c) -> (b -> c) -> Vis a b -> c
vis f g v = case v of Priv a -> f a; Pub b -> g b
  
instance Bifunctor Vis where
  bimap f g (Priv a) = Priv (f a)
  bimap f g (Pub b) = Pub (g b)
  
instance Bifoldable Vis where
  bifoldMap f g (Priv a) = f a
  bifoldMap f g (Pub b) = g b
  
instance Bitraversable Vis where
  bitraverse f g (Priv a) = Priv <$> f a
  bitraverse f g (Pub b) = Pub <$> g b
  
instance S.Local a => S.Local (Vis a b) where
  local_ = Priv . S.local_
  
instance S.Self b => S.Self (Vis a b) where
  self_ = Pub . S.self_
  
instance (S.Field a, S.Field b) => S.Field (Vis a b) where
  type Compound (Vis a b) = Vis (S.Compound a) (S.Compound b)
  p #. k = bimap (S.#. k) (S.#. k) p
  
  
-- | .. or internal or external to a file
data Res a b = In a | Ex b
  deriving (Eq, Ord, Show, Typeable, Functor, Foldable, Traversable)

instance Bifunctor Res where
  bimap f g (In a) = In (f a)
  bimap f g (Ex b) = Ex (g b)

instance Bifoldable Res where
  bifoldMap f g (In a) = f a
  bifoldMap f g (Ex b) = g b

instance Bitraversable Res where
  bitraverse f g (In a) = In <$> f a
  bitraverse f g (Ex b) = Ex <$> g b
  
instance S.Local a => S.Local (Res a b) where
  local_ = In . S.local_ 
  
instance S.Self a => S.Self (Res a b) where
  self_ = In . S.self_
  
instance S.Extern b => S.Extern (Res a b) where
  use_ = Ex . S.use_
  
  
-- | Literal strings are represented as text
--
--   TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text
    
    
-- | High level syntax expression grammar for my language
--
--   This expression form closely represents the textual form of my language.
--   After import resolution, it is checked and lowered and interpreted in a
--   core expression form. See 'Types/Expr.hs'.
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | TextLit StringExpr
  | Var a
  | Get (Field (Expr a))
  | Group (Group (Expr a))
  | Extend (Expr a) (Group (Expr a))
  | Unop S.Unop (Expr a)
  | Binop S.Binop (Expr a) (Expr a)
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

instance Applicative Expr where
  pure = return
  
  (<*>) = ap
  
instance Monad Expr where
  return = Var
  
  e >>= f = go e where
    go (IntegerLit i) = IntegerLit i
    go (NumberLit d) = NumberLit d
    go (TextLit s) = TextLit s
    go (Var a) = f a
    go (Get (e `At` k)) = Get (go e `At` k)
    go (Group b) = Group (go <$> b)
    go (Extend e b) = Extend (go e) (go <$> b)
    go (Unop op e) = Unop op (go e)
    go (Binop op e w) = Binop op (go e) (go w)
    
-- | Overload literal numbers and strings
instance Num (Expr a) where
  fromInteger = IntegerLit . fromInteger
  (+) = error "Num (Expr a)"
  (-) = error "Num (Expr a)"
  (*) = error "Num (Expr a)"
  abs = error "Num (Expr a)"
  signum = error "Num (Expr a)"
  negate = error "Num (Expr a)"
  
instance Fractional (Expr a) where
  fromRational = NumberLit . fromRational
  (/) = error "Num (Expr a)"
  
instance IsString (Expr a) where
  fromString = TextLit . fromString

instance S.Lit (Expr a) where
  unop_ = Unop
  binop_ = Binop
  
instance S.Local a => S.Local (Expr a) where
  local_ = Var . S.local_
  
instance S.Self a => S.Self (Expr a) where
  self_ = Var . S.self_
  
instance S.Extern a => S.Extern (Expr a) where
  use_ = Var . S.use_
  
instance S.Field (Expr a) where
  type Compound (Expr a) = Expr a
  e #. i = Get (e `At` K_ i)
  
instance S.Block (Expr a) where
  type Stmt (Expr a) = RecStmt (Expr a)
  block_ = Group . S.block_

instance S.Extend (Expr a) where
  type Ext (Expr a) = Group (Expr a)
  (#) = Extend
  
  
-- | Name groups are created with (recursive) block or (non-recursive)
--   tuple expressions
newtype Group a = Block [RecStmt a]
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Block (Group (Expr a)) where
  type Stmt (Group (Expr a)) = RecStmt (Expr a)
  block_ = Block


-- | Statements in a block expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
data RecStmt a =
    Decl (Path Key)
  | Patt `LetRec` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Self (RecStmt a) where
  self_ = Decl . Pure . K_
  
instance S.Field (RecStmt a) where
  type Compound (RecStmt a) = Path Key
  p #. i = Decl (p S.#. i)

instance S.Let (RecStmt a) where
  type Lhs (RecStmt a) = Patt
  type Rhs (RecStmt a) = a
  p #= a = LetRec p a
  
    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
data Stmt a =
    Pun (Vis (Path S.Ident) (Path Key))
  | Path Key `Let` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Self (Stmt a) where
  self_ = Pun . Pub . Pure . K_
  
instance S.Local (Stmt a) where
  local_ = Pun . Priv . Pure
  
instance S.Field (Stmt a) where
  type Compound (Stmt a) = Vis (Path S.Ident) (Path Key)
  p #. i = Pun (p S.#. i)

instance S.Let (Stmt a) where
  type Lhs (Stmt a) = Path Key
  type Rhs (Stmt a) = a
  p #= a = Let p a
  

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Decompose pattern (matches a set of paths to corresponding nested patterns)
--   * A decompose pattern with left over pattern (matches set of fields not
--      matched by the decompose pattern)
data Patt =
    LetPath (Vis (Path S.Ident) (Path Key))
  | Ungroup [Stmt Patt]
  | LetUngroup Patt [Stmt Patt]
  deriving (Eq, Show, Typeable)
  
instance S.Self Patt where
  self_ = LetPath . S.self_
  
instance S.Local Patt where
  local_ = LetPath . S.local_
  
instance S.Field Patt where
  type Compound Patt = Vis (Path S.Ident) (Path Key)
  p #. k = LetPath (p S.#. k)

instance S.Block Patt where
  type Stmt Patt = Stmt Patt
  block_ = Ungroup
  
instance S.Extend Patt where
  type Ext Patt = [Stmt Patt]
  e # b = LetUngroup e b

instance S.Block [Stmt Patt] where
  type Stmt [Stmt Patt] = Stmt Patt
  block_ = id


-- | A set of top level recursive statements
type Program a = [RecStmt (Expr (Name S.Ident Key a))]
  
