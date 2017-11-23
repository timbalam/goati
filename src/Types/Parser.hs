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
--  , PathPattern
--  , PatternExpr
--  , AsStmt
  , ShowMy(..)
  , Tag
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
  

-- | Extract a valid my-language source text representation from a
-- | Haskell data type representation
class ShowMy a where
  showMy :: a -> String
  showMy x = showsMy x ""
  
  showsMy :: a -> String -> String
  showsMy x s = showMy x ++ s
  
  
-- | Print a literal string
showLitString [] s =
  s

showLitString ('"' : cs) s =
  "\\\"" ++ (showLitString cs s)

showLitString (c   : cs) s =
  showLitChar c (showLitString cs s)
    
   
showLitText :: T.Text -> String -> String
showLitText = showLitString . T.unpack


type Tag = T.Text


instance ShowMy Tag where
  showsMy x s =
    showLitText x s
    
    
instance (ShowMy a, ShowMy (f (Free f a))) => ShowMy (Free f a) where
  showMy (Pure a) =
    showMy a
    
  showMy (Free f) =
    showMy f
    
    
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
  deriving (Eq, Functor)
  
  
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
    

  
instance ShowMy a => ShowMy (Expr a) where
  showsMy (IntegerLit n)        s = show n ++ s
  showsMy (NumberLit n)         s = show n ++ s
  showsMy (StringLit x)         s = showLitText x s
  showsMy (Var x)               s = showsMy x s
  showsMy (Get path)            s = showsMy path s
  showsMy (Block [])            s = "{}" ++ s
  showsMy (Block (x:xs))        s =
    "{ " ++ showsMy x (foldr showsStmt (" }" ++ s) xs)
    where
      showsStmt a x = "; " ++ showsMy a x
  showsMy (Update a b)          s = showsVal a (showsParens b s)
    where
      showsParens a             s = "(" ++ showsMy a (")" ++ s)
      showsVal a@(Unop{})       s = showsParens a s
      showsVal a@(Binop{})      s = showsParens a s
      showsVal a                s = showsMy a s
  showsMy (Unop o a)            s = showsMy o (showsOp a s)
    where 
      showsOp a@(Binop{}) s = "(" ++ showsMy a (")" ++ s)
      showsOp a                 s = showsMy a s
  showsMy (Binop o a b)         s =
    showsOp a (" " ++ showsMy o (" " ++ showsOp b s))
    where
      showsOp a@(Binop p _ _) s 
        | prec p o    = "(" ++ showsMy a (")" ++ s)
        | otherwise   = showsMy a s
      showsOp a               s = showsMy a s


instance ShowMy Unop where
  showsMy Neg   = showLitChar '-'
  showsMy Not   = showLitChar '!'


instance ShowMy Binop where
  showsMy Add   = showLitChar '+'
  showsMy Sub   = showLitChar '-'
  showsMy Prod  = showLitChar '*'
  showsMy Div   = showLitChar '/'
  showsMy Pow   = showLitChar '^'
  showsMy And   = showLitChar '&'
  showsMy Or    = showLitChar '|'
  showsMy Lt    = showLitChar '<'
  showsMy Gt    = showLitChar '>'
  showsMy Eq    = showLitString "=="
  showsMy Ne    = showLitString "!="
  showsMy Le    = showLitString "<="
  showsMy Ge    = showLitString ">="
    
        
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data Field a =
  a `At` Tag
  deriving Functor
  
  
instance Eq a => Eq (Field a) where
  a `At` x == b `At` y =
    a == b && x == y
  
  
instance ShowMy a => ShowMy (Field a) where
  showsMy (a `At` x) s =
    showsMy a ("." ++ showsMy x s)
    
    
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
  deriving (Eq, Functor)

    
instance ShowMy a => ShowMy (Stmt a) where
  showMy (Declare l) =
    showMy  l ++ " ="
    
  showMy (SetPun l) =
    showMy l
  
  showMy (l `Set` r) =
    showMy l ++ " = " ++  showMy r



-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr a =
    SetPath (Path a)
  | SetBlock [MatchStmt a]
  | SetConcat [MatchStmt a] (Path a)
  deriving (Eq, Functor)
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
data MatchStmt a =
    Path Tag `Match` SetExpr a
  | MatchPun (Path a)
  deriving (Eq, Functor)
    

instance ShowMy a => ShowMy (SetExpr a) where
  showMy (SetPath x)        = showMy x
  showMy (SetBlock [])      = "{}"
  showMy (SetBlock (x:xs))  =
    "{ " ++ showMy x ++ foldr showsStmt " }" xs
    where
      showsStmt a x = "; " ++ showsMy a x
  showMy (SetConcat stmts l) =
    "[" ++ showsBlock stmts (showsTail l "]")
    where
      showsTail a       s = "| " ++ showsMy a (" " ++ s)
      
      showsBlock []     s = s
      showsBlock (x:xs) s =
        " { " ++ showsMy x (foldr showsStmts (" } " ++ s) xs)
        
      showsStmts a      x = "; " ++ showsMy a x
      
    
    
instance ShowMy a => ShowMy (MatchStmt a) where
  showMy (r `Match` l)  = showMy r ++ " = " ++ showMy l
    
  showMy (MatchPun l)   = showMy l
    


-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
--type PathPattern = Path Tag


--newtype PatternExpr = PatternExpr (SetExpr PathPattern PatternExpr)
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
--type AsStmt = MatchStmt PathPattern PatternExpr
  
  
