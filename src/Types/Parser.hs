{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Parser
  ( Expr(..)
  , Path
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Field(..)
  , SetExpr(..)
  , MatchStmt(..)
  , Tag
  , Vis(..)
  , vis, maybePriv, maybePub
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
import Data.Functor.Classes
import Bound
  

type Tag = T.Text


-- | Binder visibility can be public or private to a scope
data Vis a = Pub a | Priv a
  deriving (Eq, Ord, Show)

vis :: (a -> b) -> (a -> b) -> Vis a -> b
vis f g (Pub a) = f a
vis f g (Priv a) = g a

maybePub = vis Just (const Nothing)

maybePriv = vis (const Nothing) Just
    
    
-- | High level syntax expression grammar for my-language
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var a
  | Get (Field (Expr a))
  | Block [Stmt a]
  | Update (Expr a) (Expr a)
  | Unop Unop (Expr a)
  | Binop Binop (Expr a) (Expr a)
  deriving (Eq, Show, Functor)
  
  
-- | Literal strings are represented as non-empty lists of text
-- | ? We could maybe add some sort of automatic interpolation
type StringExpr = T.Text

  
data Unop =
    Neg
  | Not
  deriving (Eq, Show)
  
  
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
  deriving (Eq, Show)
  

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
data Field a =
  a `At` Tag
  deriving (Show, Functor)
  
  
instance Eq a => Eq (Field a) where
  a `At` x == b `At` y =
    a == b && x == y
    
    
type Path = Free Field
 
 
-- | Statements allowed in a my-language block expression (Block constructor for Expr)
-- |  * declare a path (without a value)
-- |  * define a local path by inheriting an existing path
-- |  * set statement defines a series of paths using a computed value
data Stmt a =
    Declare (Path a)
  | SetPun (Path a) 
  | SetExpr a `Set` Expr a
  -- SetExpr (Path a) PatternExpr `Set` Expr a
  deriving (Eq, Show, Functor)


-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr a =
    SetPath (Path a)
  | SetBlock [MatchStmt a]
  | SetConcat [MatchStmt a] (Path a)
  deriving (Eq, Show, Functor)
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
data MatchStmt a =
    Path Tag `Match` SetExpr a
  | MatchPun (Path a)
  deriving (Eq, Show, Functor)
    

-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
--type PathPattern = Path Tag


--newtype PatternExpr = PatternExpr (SetExpr PathPattern PatternExpr)
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
--type AsStmt = MatchStmt PathPattern PatternExpr
  
  
