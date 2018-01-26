{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Classes
  ( ShowMy(..)
  , ReadMy(..), readMy
  , MyError(..)
  , MyException(..)
  ) where
  
import qualified Parser
import qualified Types.Parser as Parser
import qualified Expr
import qualified Types.Expr as Expr
import Types.Expr( Label, Id )
import Types.Error

  
import Data.Char( showLitChar )
import Data.Foldable( foldr )
import Data.List.NonEmpty( NonEmpty(..) )
--import Data.Functor.Identity
import Data.Typeable
import Data.Void
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Text.Parsec as P
import Control.Monad.Free
import Control.Monad.Trans
import Control.Monad.State
import Control.Exception
import Bound
  

-- | Extract a valid my-language source text representation from a
-- | Haskell data type representation
class ShowMy a where
  showMy :: a -> String
  showMy x = showsMy x ""
  
  showsMy :: a -> String -> String
  showsMy x s = showMy x ++ s
  
  
instance ShowMy Void where showMy = absurd

instance ShowMy Label where showsMy = Parser.showText

instance ShowMy Parser.Symbol where showsMy = Parser.showSymbol

instance ShowMy Parser.Tag where showsMy = Parser.showTag
  
instance ShowMy a => ShowMy (Parser.Field a) where showsMy = Parser.showField showsMy
    
instance ShowMy a => ShowMy (Parser.Path a) where showsMy = Parser.showPath showsMy
  
instance ShowMy Parser.Var where showsMy = Parser.showVar
  
instance ShowMy (Parser.Syntax a) where showsMy = Parser.showSyntax
      
instance ShowMy Parser.Unop where showsMy = Parser.showUnop
  
instance ShowMy Parser.Binop where showsMy = Parser.showBinop
    
instance ShowMy (Parser.Stmt a) where showsMy = Parser.showStmt

instance ShowMy (NonEmpty (Parser.Stmt a)) where showsMy = Parser.showProgram
  
instance ShowMy Parser.SetExpr where showsMy = Parser.showSetExpr
      
instance ShowMy Parser.MatchStmt where showsMy = Parser.showMatchStmt
      
instance (ShowMy k, ShowMy a) => ShowMy (Expr.Expr s k a) where
  showsMy (Expr.String t)       = shows t
  showsMy (Expr.Number d)       = shows d
  showsMy (Expr.Var a)          = showsMy a
  showsMy (Expr.Block{})        = errorWithoutStackTrace "showMy: Expr.Block"
  showsMy (e `Expr.At` t)       = showsMy e . showsMy t
  showsMy (e `Expr.Fix` x)      = errorWithoutStackTrace "showMy: Expr.Fix"
  showsMy (e1 `Expr.Update` e2) = errorWithoutStackTrace "showMy: Expr.Update"
  showsMy (e `Expr.AtPrim` p)   = errorWithoutStackTrace "showMy: Expr.AtPrim"
    
instance ShowMy k => ShowMy (Expr.Key k) where
  showsMy (Expr.Label l) = showChar '.' . showsMy l
  showsMy (Expr.Symbol s) = showChar '.' . showChar '(' . showsMy s . showChar ')'
  showsMy Expr.Self = errorWithoutStackTrace "showMy: Expr.Self"
  showsMy (Expr.Unop _) = errorWithoutStackTrace "showMy: Expr.Unop"
  showsMy (Expr.Binop _) = errorWithoutStackTrace "showMy: Expr.Binop"
  
  
-- | Parse source text into a my-language Haskell data type
class ReadMy a where readsMy :: Parser.Parser a
  
  
readMy :: ReadMy a => String -> a
readMy = either (errorWithoutStackTrace "readMy") id . Parser.parse (readsMy <* P.eof) "readMy" . T.pack


readIOMy :: ReadMy a => String -> IO a
readIOMy = either (ioError . userError . displayError) return
  . Parser.parse (readsMy <* P.eof) "readMy" . T.pack

              
instance ReadMy Parser.Syntax_ where readsMy = Parser.rhs
    
instance ReadMy Parser.Stmt_ where readsMy = Parser.stmt

instance ReadMy Parser.SetExpr where readsMy = Parser.lhs

instance ReadMy Parser.MatchStmt where readsMy = Parser.matchstmt
      
      
-- | Class for displaying exceptions
class MyError a where
  displayError :: a -> String
  
  
newtype MyException a = MyExceptions (NonEmpty a)
  deriving (Show, Typeable)
  
  
instance (MyError a, Show a, Typeable a) => Exception (MyException a) where
  displayException (MyExceptions (a:|as)) = displayError a ++ foldMap (("\n\n"++) . displayError) as


instance MyError Expr.ScopeError where
  displayError (Expr.ParamFree v) = "Not in scope: Variable " ++ showMy v
  displayError (Expr.SymbolFree s) = "Not in scope: Symbol " ++ showMy s
  

instance MyError Expr.ExprError where
  displayError e = case e of
    Expr.OlappedMatch perr -> "Overlapping destructuring of paths: \n" ++
      unlines (showMy <$> Expr.listPaths perr)
      
    Expr.OlappedSet v perr -> "Overlapping definitions for paths: \n" ++
      unlines (showMy <$> Expr.listPaths perr)
      
    Expr.OlappedSym s -> "Multiple definitions for symbol " ++ showMy s
      
      
instance MyError P.ParseError where
  displayError p = shows "Parse error: " (show p)
  
  
instance MyError IOError where
  displayError e = shows "IO error: " (show e)
    
