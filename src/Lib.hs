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
import Expr( expr )
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
  either
    (shows "error: " . show)
    showMy
    (P.parse program "myi" (T.pack s))
    
    
loadProgram :: FilePath -> IO (Expr (Vis Id))
loadProgram file =
  do
    s <- T.readFile file
    e <- either
      (ioError . userError . shows "parse: " . show)
      (return . flip Parser.Block Nothing . toList)
      (P.parse program file s)
    e <- either
      (ioError . userError . shows "expr: " . show)
      return
      (expr e)
    e <- maybe 
      (ioError (userError "closed"))
      return
      (closed e)
    either
      (ioError . userError . shows "eval: " . show)
      return
      (get e (Label "run"))

  
evalAndPrint :: T.Text -> IO ()
evalAndPrint s =
  do
    e <- either
      (ioError . userError . shows "parse: " . show)
      return
      (P.parse (rhs <* P.eof) "myi" s)
    e <- either
      (ioError . userError . shows "expr: " . show)
      return
      (expr e)
    e <- maybe
      (ioError (userError "closed"))
      return
      (closed e)
    either
      (ioError . userError . shows "eval: " . show)
      (putStrLn . showMy :: Expr (Vis Id) -> IO ())
      (eval e)

    
browse :: IO ()
browse =
  first
    where 
      first = readPrompt ">> " >>= rest
    
      rest ":q" = return ()
      rest s = evalAndPrint s >> first
   
