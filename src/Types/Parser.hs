{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Parser
  ( Syntax(..)
  , Block(..)
  , RecStmt(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Field(..)
  , SetExpr(..)
  , Ident
  , Path
  , Symbol(..)
  , Tag(..)
  , Var(..)
  , VarPath
  , Free(..)
  , prec
  ) where
import Data.List.NonEmpty ( NonEmpty )
import qualified Data.Text as T
import Control.Monad.Free
  

-- | Field label
type Ident = T.Text


-- | Symbol
newtype Symbol = S_ Ident
  deriving (Eq, Ord, Show)

        
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data Tag = Ident Ident | Symbol Symbol
  deriving (Eq, Ord, Show)
  
  
data Field a = a `At` Tag
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
type Path = Free Field


-- | Binder visibility can be public or private to a scope
data Var = Priv Ident | Pub Tag
  deriving (Eq, Ord, Show)
    
    
type VarPath = Path Var
    
    
-- | High level syntax expression grammar for my-language
data Syntax =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var Var
  | Get (Field Syntax)
  | Block Block
  | Extend Syntax Block
  | Unop Unop Syntax
  | Binop Binop Syntax Syntax
  deriving (Eq, Show)
    
    
-- | Recursive and pattern (non-recursive) block types
data Block = 
    Tup [Stmt Syntax]
  | Rec [RecStmt]
  deriving (Eq, Show)
    
  
-- | Literal strings are represented as non-empty lists of text
-- | TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text

  
data Unop =
    Neg
  | Not
  deriving (Eq, Ord, Show)
  
  
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
  deriving (Eq, Ord, Show)
  
  

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
data RecStmt =
    DeclSym Symbol
  | DeclVar (Path Ident) 
  | SetExpr `SetRec` Syntax
  deriving (Eq, Show)
    
    
data Stmt a =
    Pun VarPath
  | Path Tag `Set` a
  deriving (Eq, Show)


-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr =
    SetPath VarPath
  | Decomp [Stmt SetExpr]
  | SetDecomp SetExpr [Stmt SetExpr]
  deriving (Eq, Show)
  
  
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
  
  
