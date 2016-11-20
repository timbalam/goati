{-# LANGUAGE FlexibleContexts #-}
module Lib
  ( readProgram
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

readMy :: MonadError E.Error m => Parser a -> String -> m a
readMy parser input = either (throwError . E.Parser) return (P.parse parser "myc" input)

readProgram :: String -> String
readProgram s = either show showStmts (readMy program s)
  where
    showStmts (x:xs) = show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
  
evalProgram :: String -> IO String
evalProgram s =
  runExceptT (runEval (readMy program s >>= evalRval . T.Rnode) []) >>= return . either show show