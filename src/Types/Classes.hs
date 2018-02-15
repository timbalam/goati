{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Classes
  ( MyError(..)
  , MyException(..)
  ) where
  
import Parser( ShowMy(..) )
--import qualified Types.Parser as Parser
import qualified Expr
import qualified Types.Expr as Expr
import Types.Expr( Ident )
import Types.Error

  
import Data.Foldable( foldr )
--import Data.Functor.Identity
import Data.Typeable
--import Data.Void
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Text.Parsec as P
--import Control.Monad.Free
--import Control.Monad.Trans
--import Control.Monad.State
import Control.Exception
  
      
-- | Class for displaying exceptions
class MyError a where
  displayError :: a -> String
  
  
newtype MyException a = MyExceptions [a]
  deriving (Show, Typeable)
  
  
instance (MyError a, Show a, Typeable a) => Exception (MyException a) where
  displayException (MyExceptions []) = "unknown errors"
  displayException (MyExceptions (a:as)) = displayError a ++ foldMap (("\n\n"++) . displayError) as

  
{-
instance MyError Expr.DefnError where
  displayError e = case e of
    Expr.OlappedMatch perr -> "Overlapping destructuring of paths: \n" ++
      unlines (showMy <$> Expr.listPaths perr)
      
    Expr.OlappedSet v perr -> "Overlapping definitions for paths: \n" ++
      unlines (showMy <$> Expr.listPaths perr)
      
    Expr.OlappedSym s -> "Multiple definitions for symbol " ++ showMy s
-}
      
      
instance MyError P.ParseError where
  displayError p = shows "Parse error: " (show p)
  
  
instance MyError IOError where
  displayError e = shows "IO error: " (show e)
    
