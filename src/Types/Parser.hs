{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Parser
  ( Syntax(..)
  , Path
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Field(..)
  , SetExpr(..)
  , MatchStmt(..)
  , Label
  , Symbol(..)
  , Id(..)
  , Tag(..)
  , Var(..)
  , Free(..)
  , prec
  ) where
import Data.Char
  ( showLitChar )
import Data.Foldable
  ( foldr )
import Data.List.NonEmpty
  ( NonEmpty(..)
  )
import qualified Data.Text as T
import Control.Monad.Free
import Control.Monad.Trans
--import Data.Functor.Classes
--import Bound
  

-- | Field label
type Label = T.Text


-- | Symbol
newtype Symbol = S T.Text
  deriving (Eq, Ord, Show)
  
  
-- | Symbol id
newtype Id = I Word
  deriving (Bounded, Enum, Eq, Ord, Show)


-- | Binder visibility can be public or private to a scope
data Var = Priv Label | Pub Tag
  deriving (Eq, Ord, Show)
    
    
-- | High level syntax expression grammar for my-language
data Syntax =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var Var
  | Get (Field Syntax)
  | Block [Stmt]
  | Extend Syntax [Stmt]
  | Unop Unop Syntax
  | Binop Binop Syntax Syntax
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
    
        
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data Tag = Label Label | Symbol Symbol
  deriving (Eq, Ord, Show)
  
  
data Field b =
    b `At` Tag
  deriving (Eq, Show, Functor)
  
  
type Path = Free Field

-- | Statements allowed in a my-language block expression (Block constructor for Expr)
-- |  * declare a path (without a value)
-- |  * define a local path by inheriting an existing path
-- |  * set statement defines a series of paths using a computed value
data Stmt =
    DeclSym Symbol Id
  | SetPun (Path Var) 
  | SetExpr `Set` Syntax
  deriving (Eq, Show)


-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr =
    SetPath (Path Var)
  | SetBlock [MatchStmt]
  | SetDecomp SetExpr [MatchStmt]
  deriving (Eq, Show)
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
data MatchStmt =
    Path Tag `Match` SetExpr
  | MatchPun (Path Var)
  deriving (Eq, Show)
    

-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
--type PathPattern = Path Tag


--newtype PatternExpr = PatternExpr (SetExpr PathPattern PatternExpr)
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
--type AsStmt = MatchStmt PathPattern PatternExpr
  
  
