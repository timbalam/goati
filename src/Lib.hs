module Eval.Base
where

import Parser
  ( program
  , rhs
  )
import qualified Types.Error as E
import qualified Types.Parser as TP
import Types.Core
import Core
import Eval.Core

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

  
readParser :: Parser a -> String -> Either P.ParseError a
readParser parser input =
  P.parse parser "myi" (T.pack input)
 
 
readProgram :: String -> Either P.ParseError (NonEmpty (PT.Stmt (Vis Tag)) b)
readProgram =
  readParser program

  
showProgram :: String -> String
showProgram s =
  case readProgram s of
    Left e ->
      show e
      
    Right (x:|xs) ->
      showsMy x (foldr showsStmt "" xs)
      where
        showsStmt a x = ";\n\n" ++ showsMy a x
    
    
loadProgram :: String -> IO (Expr (Vis Tag))
loadProgram file =
  do
    s <- readFile file
    e <- either
      (ioError . userError . show)
      (return . PT.Block)
      (readProgram s)
    maybe
      (ioError (userError "expr"))
      return
      (expr e >>= eval)

  
readValue :: String -> Either P.ParseError (Expr (Vis Tag))
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
      (putStrLn . show)
      (expr e >>= eval)

    
browse :: IO ()
browse =
  first
    where 
      first =
        readPrompt ">> " >>= rest
    
    
      rest ":q" = return ()
      rest s = evalAndPrint s >> first
   
