{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}

-- | My language exception machinery

module My.Types.Classes
  ( MyError(..)
  , MyException(..)
  , throwLeftList, throwLeftMy
  ) where
  
import Data.Foldable (foldr)
import Data.Typeable
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Text.Parsec as P
import Control.Exception
import Control.Monad.Catch (MonadThrow(..))
  
      
-- | Class for displaying exceptions
class MyError a where
  displayError :: a -> String
  
  
newtype MyException a = MyExceptions [a]
  deriving (Show, Typeable)
  
  
instance (MyError a, Show a, Typeable a) => Exception (MyException a) where
  displayException (MyExceptions []) = "unknown errors"
  displayException (MyExceptions (a:as)) = displayError a ++ foldMap (("\n\n"++) . displayError) as
  
    
throwLeftMy
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either a b -> m b
throwLeftMy = either (throwM . MyExceptions . pure) return

throwLeftList
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either [a] b -> m b
throwLeftList = either (throwM . MyExceptions) return

  
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
    
