module Main where

import Version( myiReplVersion )
import Lib
  ( runProgram
  , browse, interpret
  , K, Expr
  )
  
import System.Environment ( getArgs )
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Void

  
main :: IO ()
main =
  do
    args <- getArgs
    case args of
      [] -> runRepl
      (file:args) -> runOne (file:|args)
      
      

runRepl :: IO ()
runRepl = interpret browse []

    
runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  runProgram [] file >>= (putStrLn . show :: Expr K Void -> IO ())
