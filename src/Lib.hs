{-# LANGUAGE FlexibleContexts #-}
module Lib
  ( readProgram
  , showProgram
  ) where
import Parser
  ( program
  )
import Eval
  ( evalRval
  )
import Text.Parsec.String
  ( Parser
  )
import Control.Monad.Except
  ( MonadError
  , throwError
  , runExceptT
  )
import System.IO
  ( putStr
  , hFlush
  , stdout
  )
  
import qualified Types.Parser as T
import qualified Text.Parsec as P
import qualified Error as E
import Types.Eval
  ( IOExcept
  , runEval
  , runIOExcept
  , runValue
  )
  
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

readParser :: Parser a -> String -> Either E.Error a
readParser parser input = either (throwError . E.Parser "parse error") return (P.parse parser "myc" input)
  
readProgram :: String -> Either E.Error T.Rval
readProgram input = T.Rnode <$> readParser program input

showProgram :: String -> String
showProgram s = either show showStmts (readProgram s)
  where
    showStmts (T.Rnode (x:xs)) = show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
    
evalProgram :: String -> IO String
evalProgram s =
  runIOExcept
    (either throwError (fmap show . runValue . runEval . evalRval) (readProgram s))
    (return . show)