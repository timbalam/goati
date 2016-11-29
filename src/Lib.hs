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
  )

readProgram :: MonadError E.Error m => String -> m T.Rval
readProgram input = either (throwError . E.Parser) (return . T.Rnode) (P.parse program "myc" input)

showProgram :: String -> String
showProgram s = either show showStmts (readProgram s)
  where
    showStmts (T.Rnode (x:xs)) = show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
  
evalProgram :: String -> IO String
evalProgram s =
  runEval (readProgram s >>= evalRval) ([], []) >>= return . either show show