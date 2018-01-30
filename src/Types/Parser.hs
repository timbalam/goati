{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Parser
  ( Syntax(..), showSyntax
  , Block(..), showBlock
  , RecStmt(..), showRecStmt, showProgram
  , Stmt(..), showStmt
  , Unop(..), showUnop
  , Binop(..), showBinop
  , Field(..), showField
  , SetExpr(..), showSetExpr
  , MatchStmt(..), showMatchStmt
  , Label
  , Path, showPath
  , showText
  , Symbol(..), showSymbol
  , Tag(..), showTag
  , Var(..), showVar
  , VarPath, showVarPath 
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
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import qualified Data.Text as T
import Control.Monad.Free
import Control.Monad.Trans

  
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
    
    
type VarPath = Path Var

showVarPath :: VarPath -> ShowS
showVarPath = showPath showVar
    
    
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
  
  
showSyntax :: Syntax -> ShowS
showSyntax e = case e of
  IntegerLit n -> shows n
  NumberLit n  -> shows n
  StringLit x  -> showChar '"' . showLitText x . showChar '"'
  Var x        -> showVar x
  Get path     -> showField showSyntax path
  Block b     -> showBlock b
  Extend e b  -> showParen t (showSyntax e) . showChar ' ' . showBlock b where
    t = case e of Unop{} -> True; Binop{} -> True; _ -> False
  Unop o a     -> showUnop o . showParen t (showSyntax a)  where 
    t = case a of Binop{} -> True; _ -> False
  Binop o a b  -> showArg a . showChar ' ' . showBinop o
    . showChar ' ' . showArg b where
      showArg a = showParen t (showSyntax a) where 
        t = case a of Binop p _ _ -> prec p o; _ -> False
    
    
-- | Recursive and pattern (non-recursive) block types
data Block = 
    Tup [Stmt] (Maybe Syntax)
  | Rec [RecStmt]
  deriving (Eq, Show)
  
  
showBlock :: Block -> ShowS
showBlock b = case b of
  Tup [] Nothing -> showString "()"
  Tup [SetPun p] Nothing -> showString "( " . showPath showVar p . showString ",)"
  Tup xs m -> showChar '(' . showJustStmts xs . maybe id showPack m . showChar ')'
  Rec [] -> showString "{}"
  Rec (y:ys) -> showString "{ " . showRecStmt y . sepShowRecStmts ys . showString " }"
  where
    showJustStmts (x:xs) = showChar ' ' . showStmt x . flip (foldr sepShowStmt) xs . showChar ' '
    showJustStmts [] = id
    
    sepShowStmt stmt = showString ", " . showStmt stmt
    showPack e = showString "... " . showSyntax e . showChar ' '
    
    sepShowRecStmts  = flip (foldr sepShowRecStmt)
    sepShowRecStmt stmt = showString "; " . showRecStmt stmt
    
  
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
data RecStmt =
    DeclSym Symbol
  | DeclVar (Path Label) 
  | SetExpr `SetRec` Syntax
  deriving (Eq, Show)
  
  
showRecStmt :: RecStmt -> ShowS
showRecStmt (DeclSym s) = showSymbol s
showRecStmt (DeclVar l)  = showPath (showTag . Label) l
showRecStmt (l `SetRec` r) = showSetExpr l . showString " = " . showSyntax r
  
  
showProgram :: NonEmpty RecStmt -> ShowS
showProgram (x:|xs) = showRecStmt x  . flip (foldr sepShowRecStmt) xs
  where
    sepShowRecStmt a = showString ";\n\n" . showRecStmt a
    
    
data Stmt =
    SetPun VarPath
  | Path Tag `Set` Syntax
  deriving (Eq, Show)
  
  
showStmt :: Stmt -> ShowS
showStmt (SetPun l) = showVarPath l
showStmt (l `Set` e) = showPath showTag l . showString " = " . showSyntax e


-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr =
    SetPath VarPath
  | SetBlock [MatchStmt] (Maybe SetExpr)
  deriving (Eq, Show)
  

showSetExpr :: SetExpr -> ShowS
showSetExpr e = case e of
  SetPath x -> showVarPath x
  SetBlock [] Nothing -> showString "{}"
  SetBlock xs l -> showString "{#" . showMatchStmts xs . maybe id showDecomp l
    . showString "#}"
  where
    showMatchStmts []     = id
    showMatchStmts (x:xs) = showChar ' ' . showMatchStmt x
      . sepShowMatchStmts xs . showChar ' '
      
    sepShowMatchStmts = flip (foldr sepShowMatchStmt)
      
    showDecomp l = showString "... " . showSetExpr l . showChar ' '
    sepShowMatchStmt stmt = showString ", " . showMatchStmt stmt
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
data MatchStmt =
    Path Tag `Match` SetExpr
  | MatchPun VarPath
  deriving (Eq, Show)
  

showMatchStmt :: MatchStmt -> ShowS
showMatchStmt (MatchPun l)  = showVarPath l
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
  
  
