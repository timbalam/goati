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
  
import qualified Types.Parser as T
import qualified Text.Parsec as P
import qualified Error as E
import Types.Eval
  ( runEval
  , runIOExcept
  , runValue
  )
  
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

readParser :: P.Parser a -> String -> IOExcept a
readParser parser input = either (throwError . E.Parser "parse error") return (P.parse parser "myc" input)
  
readProgram :: String -> IOExcept T.Rval
readProgram input = T.Rnode <$> readParser program

showProgram :: String -> String
showProgram s = either show showStmts (readProgram s)
  where
    showStmts (T.Rnode (x:xs)) = show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
    
evalProgram :: String -> IO String
evalProgram s =
  runIOExcept
    (readProgram s >>= fmap show . runValue . runEval . evalRval)
    (return . show)