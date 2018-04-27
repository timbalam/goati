{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}

-- | Types of my language syntax
module My.Types.Parser
  ( Expr(..)
  , Group(..)
  , RecStmt(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Field(..)
  , Patt(..)
  , Program(..)
  , Ident(..)
  , Key(..)
  , StringExpr
  , Path
  , Import(..)
  , Vis(..)
  , Res(..)
  , Name
  , VarPath
  , Free(..)
  , prec
  ) where
import qualified Data.Text as T
import Control.Monad.Free
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Typeable
import Data.List.NonEmpty (NonEmpty)
import Data.String (IsString(..))
import My.Util
  

newtype Ident = I_ T.Text
  deriving (Eq, Ord, Show, Typeable)
  
  
instance IsString Ident where
  fromString = I_ . fromString

  
newtype Key = K_ Ident
  deriving (Eq, Ord, Show, Typeable)
  
  
instance IsString Key where
  fromString = K_ . fromString
  
  
newtype Import = Use Ident
  deriving (Eq, Ord, Show, Typeable)
  
  
-- | Alias for typical variable name type
type Name a b = Res (Vis a b)


-- | Alias for typical set target type
type VarPath = Vis (Path Ident) (Path Key)
 
 
-- | A path expression for my language recursively describes a set of nested
--   fields relative to a self- or environment-defined field
type Path = Free Field


data Field a = a `At` Key
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)


-- | Binder visibility can be public or private to a scope
data Vis a b = Priv a | Pub b
  deriving (Eq, Ord, Show, Typeable, Functor, Foldable, Traversable)
  
  
instance Bifunctor Vis where
  bimap f g (Priv a) = Priv (f a)
  bimap f g (Pub b) = Pub (g b)
  
instance Bifoldable Vis where
  bifoldMap f g (Priv a) = f a
  bifoldMap f g (Pub b) = g b
  
instance Bitraversable Vis where
  bitraverse f g (Priv a) = Priv <$> f a
  bitraverse f g (Pub b) = Pub <$> g b
  
  
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
    
    
-- | High level syntax expression grammar for my language
--
--   This expression form closely represents the textual form of my language.
--   After import resolution, it is checked and lowered and interpreted in a
--   core expression form. See 'Types/Expr.hs'.
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var a
  | Get (Field (Expr a))
  | Group (Group (Expr a))
  | Extend (Expr a) (Group (Expr a))
  | Unop Unop (Expr a)
  | Binop Binop (Expr a) (Expr a)
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  

instance Applicative Expr where
  pure = return
  
  (<*>) = ap
  
instance Monad Expr where
  return = Var
  
  e >>= f = go e where
    go (IntegerLit i) = IntegerLit i
    go (NumberLit d) = NumberLit d
    go (StringLit s) = StringLit s
    go (Var a) = f a
    go (Get (e `At` k)) = Get (go e `At` k)
    go (Group b) = Group (go <$> b)
    go (Extend e b) = Extend (go e) (go <$> b)
    go (Unop op e) = Unop op (go e)
    go (Binop op e w) = Binop op (go e) (go w)
  
    
-- | Name groups are created with (recursive) block or (non-recursive)
--   tuple expressions
data Group a =
    Tup [Stmt a]
  | Block [RecStmt a]
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
  
-- | Literal strings are represented as text
--
--   TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text

  
-- | Unary operators
data Unop =
    Neg
  | Not
  deriving (Eq, Ord, Show, Typeable)
  
  
-- | Binary operators
data Binop =
    Add
  | Sub
  | Prod
  | Div
  | Pow
  | And
  | Or
  | Lt
  | Gt 
  | Eq
  | Ne
  | Le
  | Ge
  deriving (Eq, Ord, Show, Typeable)
  
  

-- | a `prec` b is True if a has higher precedence than b
--
-- TODO: Implement relative precedence??
prec :: Binop -> Binop -> Bool
prec _    Pow   = False
prec Pow  _     = True
prec _    Prod  = False
prec _    Div   = False
prec Prod _     = True
prec Div  _     = True
prec _    Add   = False
prec _    Sub   = False
prec Add  _     = True
prec Sub  _     = True
prec _    Eq    = False
prec _    Ne    = False
prec _    Lt    = False
prec _    Gt    = False
prec _    Le    = False
prec _    Ge    = False
prec Eq   _     = True
prec Ne   _     = True
prec Lt   _     = True
prec Gt   _     = True
prec Le   _     = True
prec Ge   _     = True
prec _    And   = False
prec And  _     = True
prec _    Or    = False
--prec Or   _     = True


-- | Statements in a block expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
data RecStmt a =
    Decl (Path Key)
  | Patt `LetRec` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
data Stmt a =
    Pun (Vis (Path Ident) (Path Key))
  | Path Key `Let` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Decompose pattern (matches a set of paths to corresponding nested patterns)
--   * A decompose pattern with left over pattern (matches set of fields not
--      matched by the decompose pattern)
data Patt =
    LetPath (Vis (Path Ident) (Path Key))
  | Des [Stmt Patt]
  | LetDes Patt [Stmt Patt]
  deriving (Eq, Show, Typeable)


-- | A program guaranteed to be a non-empty set of top level recursive statements
--   with an optional initial global import
data Program a =
  Program
    (Maybe a)
    (NonEmpty (RecStmt (Expr (Name Ident Key a))))
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
  
