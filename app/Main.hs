module Main where

import Version( myiReplVersion )
import Lib
  ( runFile
  , browse
  , K, Expr
  )
  
import qualified System.Directory
import qualified System.Environment
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Void

  
main :: IO ()
main =
  do
    args <- System.Environment.getArgs
    case args of
      [] -> runRepl
      (file:args) -> runOne (file:|args)
      
      

runRepl :: IO ()
runRepl = System.Directory.getCurrentDirectory >>= browse . pure

    
runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  runFile file [] >>= (putStrLn . show :: Expr K Void -> IO ())
