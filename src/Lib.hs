{-# LANGUAGE OverloadedStrings #-}
module Lib
  ( showProgram
  , loadProgram
  , browse
  , module Types
  )
where

import Parser
  ( program
  , rhs
  )
--import qualified Types.Error as E
import qualified Types.Parser as Parser
import Types
import Core( expr )
import Eval( eval )

import qualified Data.Map as M
import System.IO
  ( hFlush
  , stdout
  , FilePath
  )
import Data.List.NonEmpty( NonEmpty(..), toList )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Text.Parsec.Text ( Parser )
import qualified Text.Parsec as P

  
-- Console / Import --
flushStr :: T.Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: T.Text -> IO (T.Text)
readPrompt prompt =
  flushStr prompt >> T.getLine

  
showProgram :: String -> String
showProgram s =
  case P.parse program "myi" (T.pack s) of
    Left e ->
      show e
      
    Right r ->
      showMy r
    
    
loadProgram :: FilePath -> IO (Expr (Vis Tag))
loadProgram file =
  do
    s <- T.readFile file
    e <- either
      (ioError . userError . show)
      (return . Parser.Block . toList)
      (P.parse program file s)
    maybe
      (ioError (userError "expr"))
      return
      (getresult (expr e) >>= eval)

  
evalAndPrint :: T.Text -> IO ()
evalAndPrint s =
  do
    e <- either
      (ioError . userError . show)
      return
      (P.parse (rhs <* P.eof) "myi" s)
    maybe
      (ioError (userError "expr"))
      (putStrLn . showMy)
      (getresult (expr e) >>= eval)

    
browse :: IO ()
browse =
  first
    where 
      first = readPrompt ">> " >>= rest
    
      rest ":q" = return ()
      rest s = evalAndPrint s >> first
   
