{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Parser
  ( Syntax(..), showSyntax
  , Stmt(..), showStmt, showProgram
  , Unop(..), showUnop
  , Binop(..), showBinop
  , Field(..), showField
  , SetExpr(..), showSetExpr
  , MatchStmt(..), showMatchStmt
  , Label, Syntax_, Stmt_
  , Path, showPath
  , showText
  , Symbol(..), showSymbol
  , Tag(..), showTag
  , Var(..), showVar
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


-- | Useful alias
type Syntax_ = Syntax ()
type Stmt_ = Stmt ()

  
-- | Utility functions for printing string literals
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)
    
    
showLitText :: T.Text -> String -> String
showLitText = showLitString . T.unpack
  

-- | Field label
type Label = T.Text


showText :: T.Text -> ShowS
showText = (++) . T.unpack


-- | Symbol
newtype Symbol = S_ T.Text
  deriving (Eq, Ord, Show)
  
  
showSymbol :: Symbol -> ShowS
showSymbol (S_ s) = showChar '\'' . showText s

        
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data Tag = Label Label | Symbol Symbol
  deriving (Eq, Ord, Show)
  
  
data Field a = a `At` Tag
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
type Path = Free Field


showTag :: Tag -> ShowS
showTag (Label l) = showChar '.' . showText l
showTag (Symbol s) = showChar '.' . showChar '(' . showSymbol s . showChar ')'
  
  
showField :: (a -> ShowS) -> Field a -> ShowS
showField showa (a `At` t) = showa a . showTag t


showPath :: (a -> ShowS) -> Path a -> ShowS
showPath showa (Pure a) = showa a
showPath showa (Free f) = showField (showPath showa) f


-- | Binder visibility can be public or private to a scope
data Var = Priv Label | Pub Tag
  deriving (Eq, Ord, Show)
  
  
showVar :: Var -> ShowS
showVar (Priv l) = showText l
showVar (Pub t) = showTag t
    
    
-- | High level syntax expression grammar for my-language
data Syntax a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var Var
  | Get (Field (Syntax a))
  | Block [Stmt a]
  | Extend (Syntax a) [Stmt a]
  | Unop Unop (Syntax a)
  | Binop Binop (Syntax a) (Syntax a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
showSyntax :: Syntax a -> ShowS
showSyntax e = case e of
  IntegerLit n -> shows n
  NumberLit n  -> shows n
  StringLit x  -> showChar '"' . showLitText x . showChar '"'
  Var x        -> showVar x
  Get path     -> showField showSyntax path
  Block xs     -> showBlock xs
  Extend e xs  -> showParen t (showSyntax e) . showChar ' ' . showBlock xs where
    t = case e of Unop{} -> True; Binop{} -> True; _ -> False
  Unop o a     -> showUnop o . showParen t (showSyntax a)  where 
    t = case a of Binop{} -> True; _ -> False
  Binop o a b  -> showArg a . showChar ' ' . showBinop o
    . showChar ' ' . showArg b where
      showArg a = showParen t (showSyntax a) where 
        t = case a of Binop p _ _ -> prec p o; _ -> False
  where
    showBlock [] = showString "{}"
    showBlock (x:xs) = showString "{ " . showStmt x
      . flip (foldr sepShowStmt) xs . showString " }"
  
    sepShowStmt a = showString "; " . showStmt a
  
  
-- | Literal strings are represented as non-empty lists of text
-- | TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text

  
data Unop =
    Neg
  | Not
  deriving (Eq, Ord, Show)
  
  
showUnop :: Unop -> ShowS
showUnop Neg = showChar '-'
showUnop Not = showChar '!'
  
  
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

  
showBinop :: Binop -> ShowS
showBinop Add   = showChar '+'
showBinop Sub   = showChar '-'
showBinop Prod  = showChar '*'
showBinop Div   = showChar '/'
showBinop Pow   = showChar '^'
showBinop And   = showChar '&'
showBinop Or    = showChar '|'
showBinop Lt    = showChar '<'
showBinop Gt    = showChar '>'
showBinop Eq    = showString "=="
showBinop Ne    = showString "!="  
showBinop Le    = showString "<="
showBinop Ge    = showString ">="


-- | Statements allowed in a my-language block expression (Block constructor for Expr)
-- |  * declare a path (without a value)
-- |  * define a local path by inheriting an existing path
-- |  * set statement defines a series of paths using a computed value
data Stmt a =
    DeclSym Symbol a
  | SetPun (Path Var) 
  | SetExpr `Set` Syntax a
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
showStmt :: Stmt a -> ShowS
showStmt (DeclSym s _) = showSymbol s
showStmt (SetPun l)  = showPath showVar l
showStmt (l `Set` r) = showSetExpr l . showString " = " . showSyntax r
  
  
showProgram :: NonEmpty (Stmt a) -> ShowS
showProgram (x:|xs) = showStmt x  . flip (foldr sepShowStmt) xs
  where
    sepShowStmt a = showString ";\n\n" . showStmt a


-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr =
    SetPath (Path Var)
  | SetBlock [MatchStmt]
  | SetDecomp SetExpr [MatchStmt]
  deriving (Eq, Show)
  

showSetExpr :: SetExpr -> ShowS
showSetExpr e = case e of
  SetPath x -> showPath showVar x
  SetBlock xs -> showBlock xs Nothing
  SetDecomp l xs -> showBlock xs (Just l)
  where
    showBlock []     m = showChar '{' . maybe (showChar '}') showTail m
    showBlock (x:xs) m = showString "{ " . showMatchStmt x
      . flip (foldr sepShowStmt) xs . maybe (showString " }") showTail m
    sepShowStmt a = showString "; " . showMatchStmt a
    showTail l = showString "... " . showSetExpr l . showString " }"
  
  
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
  

showMatchStmt :: MatchStmt -> ShowS
showMatchStmt (MatchPun l)  = showPath showVar l
showMatchStmt (r `Match` l) = showPath showTag r . showString " = " . showSetExpr l
    

-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
--type PathPattern = Path Tag


--newtype PatternExpr = PatternExpr (SetExpr PathPattern PatternExpr)
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
--type AsStmt = MatchStmt PathPattern PatternExpr
  
  
