{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Classes
  ( MyError(..)
  , MyException(..)
  ) where
  
import qualified Parser
import qualified Types.Parser as Parser
import qualified Expr
import qualified Types.Expr as Expr
import Types.Expr( Label, Id )
import Types.Error

  
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
  

  
  
instance ShowMy Void where showMy = absurd

      
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
    
