module Lib
  ( readProgram
  , showProgram
  , loadProgram
  , readValue
  , browse
  , module Types.Core
  )
where

import Parser
  ( readParser
  , program
  , rhs
  )
import qualified Types.Error as E
import qualified Types.Parser as TP
import Types.Core
import Core( expr )
import Eval( eval )

import qualified Data.Map as M
import System.IO
  ( putStr
  , hFlush
  , stdout
  )
import Data.List.NonEmpty
import qualified Data.Text as T
import Text.Parsec.Text ( Parser )
import qualified Text.Parsec as P


   
   
  
-- Console / Import --
flushStr :: String -> IO ()
flushStr str =
  putStr str >> hFlush stdout

  
readPrompt :: String -> IO String
readPrompt prompt =
  flushStr prompt >> getLine
 
 
readProgram :: String -> Either P.ParseError (NonEmpty (TP.Stmt (Vis Tag)))
readProgram =
  readParser program

  
showProgram :: String -> String
showProgram s =
  case readProgram s of
    Left e ->
      show e
      
    Right r ->
      showMy r
    
    
loadProgram :: String -> IO (Expr (Vis Tag))
loadProgram file =
  do
    s <- readFile file
    e <- either
      (ioError . userError . show)
      (return . TP.Block . toList)
      (readProgram s)
    maybe
      (ioError (userError "expr"))
      return
      (getresult (expr e) >>= eval)

  
readValue :: String -> Either P.ParseError (TP.Expr (Vis Tag))
readValue =
  readParser (rhs <* P.eof)

  
evalAndPrint :: String -> IO ()
evalAndPrint s =
  do
    e <- either
      (ioError . userError . show)
      return
      (readValue s)
    maybe
      (ioError (userError "expr"))
      (putStrLn . showMy)
      (getresult (expr e) >>= eval)

    
browse :: IO ()
browse =
  first
    where 
      first =
        readPrompt ">> " >>= rest
    
    
      rest ":q" = return ()
      rest s = evalAndPrint s >> first
   
