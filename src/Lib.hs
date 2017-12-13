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
import Eval( get, eval )

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
import Bound( closed )


type Exp = Expr (Vis Id)

  
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
    
    
loadProgram :: FilePath -> IO (Expr (Vis Id))
loadProgram file =
  do
    s <- T.readFile file
    e <- either
      (ioError . userError . show)
      (return . flip Parser.Block Nothing . toList)
      (P.parse program file s)
    e <- maybe
      (ioError (userError "expr"))
      return
      (getresult (expr e))
    e <- maybe 
      (ioError (userError "closed"))
      return
      (closed e)
    maybe
      (ioError (userError "eval"))
      return
      (get e (Label "run"))

  
evalAndPrint :: T.Text -> IO ()
evalAndPrint s =
  do
    e <- either
      (ioError . userError . show)
      return
      (P.parse (rhs <* P.eof) "myi" s)
    e <- maybe
      (ioError (userError "expr"))
      return
      (getresult (expr e))
    e <- maybe
      (ioError (userError "closed"))
      return
      (closed e)
    maybe
      (ioError (userError "eval"))
      (putStrLn . showMy :: Expr (Vis Id) -> IO ())
      (eval e)

    
browse :: IO ()
browse =
  first
    where 
      first = readPrompt ">> " >>= rest
    
      rest ":q" = return ()
      rest s = evalAndPrint s >> first
   
