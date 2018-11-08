module Main where

import Goat.Version (myiReplVersion)
import Goat.Interpreter (runFile, browse)
import qualified System.Directory
import qualified System.Environment
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void

  
main :: IO ()
main =
  do
    args <- System.Environment.getArgs
    case args of
      [] -> runRepl
      (file:args) -> runOne (file:|args)
      
      

runRepl :: IO ()
runRepl = --System.Directory.getCurrentDirectory >>=
  browse

    
runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  runFile file >> return ()
