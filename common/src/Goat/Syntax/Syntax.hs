{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, TypeFamilies #-}

-- | This module provides a mostly-depreciated set of concrete types for representing Goat syntax.
-- The types in this module are replaced by the typeclass encoding of the Goat syntax from Goat.Types.Syntax.Class.
-- However, they have been given implementations of the syntax classes and are a useful concrete representation for testing parsers.
module Goat.Syntax.Syntax
  ( Expr(..)
  , Group(..)
  , Stmt(..)
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
  , Tern(..)
  , Name
  , VarPath
  , Free(..)
  --, S.prec
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
type Name a b = Tern Import (Vis a b)


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
  
instance S.Extern_ Import where
  use_ = Use
 
 
-- | A path expression for my language recursively describes a set of nested
--   fields relative to a self- or environment-defined field
type Path = Free Field

data Field a = a `At` Key
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Field_ (Free Field a) where
  type Compound (Free Field a) = Free Field a
  p #. i = Free (p `At` K_ i)

instance S.Local a => S.Local (Free Field a) where
  local_ = Pure . S.local_
  
instance S.Self a => S.Self (Free Field a) where
  self_ = Pure . S.self_

-- | Binder visibility can be public or private to a scope
data Vis a b = Pub a | Priv b
  deriving (Eq, Ord, Show, Typeable, Functor, Foldable, Traversable)
  
vis :: (a -> c) -> (b -> c) -> Vis a b -> c
vis f g v = case v of Pub a -> f a; Priv b -> g b
  
instance Bifunctor Vis where
  bimap f g (Pub a) = Pub (f a)
  bimap f g (Priv b) = Priv (g b)
  
instance Bifoldable Vis where
  bifoldMap f g (Pub a) = f a
  bifoldMap f g (Priv b) = g b
  
instance Bitraversable Vis where
  bitraverse f g (Pub a) = Pub <$> f a
  bitraverse f g (Priv b) = Priv <$> g b
  
instance S.Local b => S.Local (Vis a b) where
  local_ = Priv . S.local_
  
instance S.Self a => S.Self (Vis a b) where
  self_ = Pub . S.self_
  
instance (S.Field a, S.Field b) => S.Field_ (Vis a b) where
  type Compound (Vis a b) = Vis (S.Compound a) (S.Compound b)
  p #. k = bimap (S.#. k) (S.#. k) p
  
  
-- | .. or internal or external to a file
data Tern a b = Ex a | In b
  deriving (Eq, Ord, Show, Typeable, Functor, Foldable, Traversable)

instance Bifunctor Tern where
  bimap f g (Ex a) = Ex (f a)
  bimap f g (In b) = In (g b)

instance Bifoldable Tern where
  bifoldMap f g (Ex a) = f a
  bifoldMap f g (In b) = g b

instance Bitraversable Tern where
  bitraverse f g (Ex a) = Ex <$> f a
  bitraverse f g (In b) = In <$> g b
  
instance S.Local b => S.Local (Tern a b) where
  local_ = In . S.local_ 
  
instance S.Self b => S.Self (Tern a b) where
  self_ = In . S.self_
  
instance S.Extern_ a => S.Extern_ (Tern a b) where
  use_ = Ex . S.use_
  
  
-- | Literal strings are represented as text
--
-- TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text
  

-- | Wrapper type for an escaped expression
newtype Esc a = Esc a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance S.Esc (Esc a) where
  type Lower (Esc a) = a
  esc_ = Esc
    
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form. See 'Types/Expr.hs'.
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | TextLit StringExpr
  | Var a
  | Lift (Esc (Expr a))
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
    go (Lift (Esc e)) = Lift (Esc (go e))
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

instance S.Un_ (Expr a) where
  neg_ = Unop S.Neg
  not_ = Unop S.Not
  
instance S.ArithB_ (Expr a) where
  (#+) = Binop S.Add
  (#-) = Binop S.Sub
  (#*) = Binop S.Prod
  (#/) = Binop S.Div
  (#^) = Binop S.Pow
  
instance S.CmpB_ (Expr a) where
  (#==) = Binop S.Eq
  (#!=) = Binop S.Ne
  (#<)  = Binop S.Lt
  (#<=) = Binop S.Le
  (#>)  = Binop S.Gt
  (#>=) = Binop S.Ge

instance S.LogicB_ (Expr a) where
  (#||) = Binop S.Or
  (#&&) = Binop S.And
  
instance S.Local a => S.Local (Expr a) where
  local_ = Var . S.local_
  
instance S.Self a => S.Self (Expr a) where
  self_ = Var . S.self_
  
instance S.Extern_ a => S.Extern_ (Expr a) where
  use_ = Var . S.use_
  
instance S.Field_ (Expr a) where
  type Compound (Expr a) = Expr a
  e #. i = Get (e `At` K_ i)
  
instance S.Esc (Expr a) where
  type Lower (Expr a) = Expr a
  esc_ = Lift . S.esc_
  
instance S.Block (Expr a) where
  type Stmt (Expr a) = Stmt (Expr a)
  block_ = Group . S.block_

instance S.Extend_ (Expr a) where
  type Ext (Expr a) = Group (Expr a)
  (#) = Extend
  
  
-- | Name groups are created with (recursive) block or (non-recursive)
--   tuple expressions
newtype Group a = Block [Stmt a]
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Block (Group (Expr a)) where
  type Stmt (Group (Expr a)) = Stmt (Expr a)
  block_ = Block


-- | Statements in a block expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--   * Recursive let statement (define a pattern to be equal to a value)
data Stmt a =
    Decl (Path Key)
  | LetPatt (Let Patt a)
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Self (Stmt a) where
  self_ = Decl . Pure . K_
  
instance S.Field_ (Stmt a) where
  type Compound (Stmt a) = Path Key
  p #. i = Decl (p S.#. i)
  
instance S.Esc (Stmt a) where
  type Lower (Stmt a) = Vis (Path Key) (Path S.Ident)
  esc_ = LetPatt . S.esc_

instance S.Let (Stmt a) where
  type Lhs (Stmt a) = Patt
  type Rhs (Stmt a) = a
  p #= a = LetPatt (p S.#= a)
  
    
-- | Statements in a match pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
data Let l r =
    Pun (Esc (Vis (Path Key) (Path S.Ident)))
  | Let l r
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Esc (Let l r) where
  type Lower (Let l r) = Vis (Path Key) (Path S.Ident)
  esc_ = Pun . S.esc_

instance S.Let (Let l r) where
  type Lhs (Let l r) = l
  type Rhs (Let l r) = r
  p #= a = Let p a
  

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Decompose pattern (matches a set of paths to corresponding nested patterns)
--   * A decompose pattern with left over pattern (matches set of fields not
--      matched by the decompose pattern)
data Patt =
    LetPath (Vis (Path Key) (Path S.Ident))
  | Decomp [Let (Path Key) (Esc Patt)]
  | LetDecomp Patt [Let (Path Key) (Esc Patt)]
  deriving (Eq, Show, Typeable)
  
instance S.Self Patt where
  self_ = LetPath . S.self_
  
instance S.Local Patt where
  local_ = LetPath . S.local_
  
instance S.Field_ Patt where
  type Compound Patt = Vis (Path Key) (Path S.Ident)
  p #. k = LetPath (p S.#. k)

instance S.Block Patt where
  type Stmt Patt = Let (Path Key) (Esc Patt)
  block_ = Decomp
  
instance S.Extend_ Patt where
  type Ext Patt = [Let (Path Key) (Esc Patt)]
  e # b = LetDecomp e b

instance S.Block [Let (Path Key) (Esc Patt)] where
  type Stmt [Let (Path Key) (Esc Patt)] = Let (Path Key) (Esc Patt)
  block_ = id


-- | A set of top level recursive statements
type Program = [Stmt (Expr (Name Key S.Ident))]

