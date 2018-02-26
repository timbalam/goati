{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Parser
  ( Expr(..)
  , Block(..)
  , RecStmt(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Field(..)
  , SetExpr(..)
  , Program(..)
  , Ident
  , Key(..)
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
import Control.Applicative( liftA2 )
import Control.Monad( ap )
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Typeable
import Data.List.NonEmpty( NonEmpty )

import Util
  

-- | Identifier
type Ident = T.Text


-- | Field key
newtype Key = K_ Ident
  deriving (Eq, Ord, Show, Typeable)
  
  
-- | Import
newtype Import = Use Ident
  deriving (Eq, Ord, Show, Typeable)
  
  
-- | Aliases for parser
type Name a b = Res (Vis a b)
--type Var = Vis Ident Key
type VarPath = Vis (Path Ident) (Path Key)
 
        
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data Field a = a `At` Key
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
type Path = Free Field


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
    
    
-- | High level syntax expression grammar for my-language
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var a
  | Get (Field (Expr a))
  | Block (Block (Expr a))
  | Extend (Expr a) (Block (Expr a))
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
    go (Block b) = Block (go <$> b)
    go (Extend e b) = Extend (go e) (go <$> b)
    go (Unop op e) = Unop op (go e)
    go (Binop op e w) = Binop op (go e) (go w)
  
    
-- | Recursive and pattern (non-recursive) block types
data Block a =
    Tup [Stmt a]
  | Rec [RecStmt a]
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
  
-- | Literal strings are represented as non-empty lists of text
-- | TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text

  
data Unop =
    Neg
  | Not
  deriving (Eq, Ord, Show, Typeable)
  
  
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
  
  

-- a `prec` b is True if a has higher precedence than b
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


-- | Statements allowed in a my-language block expression (Block constructor for Expr)
-- |  * declare a path (without a value)
-- |  * define a local path by inheriting an existing path
-- |  * set statement defines a series of paths using a computed value
data RecStmt a =
    DeclVar (Path Key) 
  | SetExpr `SetRec` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
    
data Stmt a =
    Pun (Vis (Path Ident) (Path Key))
  | Path Key `Set` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  

-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr =
    SetPath (Vis (Path Ident) (Path Key))
  | Decomp [Stmt SetExpr]
  | SetDecomp SetExpr [Stmt SetExpr]
  deriving (Eq, Show, Typeable)
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
-- type MatchStmt = Stmt SetExpr
    

-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
--type PathPattern = Path Tag


--newtype PatternExpr = PatternExpr (SetExpr PathPattern PatternExpr)
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
--type AsStmt = MatchStmt PathPattern PatternExpr


data Program a =
  Program
    (Maybe a)
    (NonEmpty (RecStmt (Expr (Name Ident Key a))))
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
  
