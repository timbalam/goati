module Main where


import Version( myiReplVersion )
import Lib
  ( runProgram
  , browse, interpret
  , ShowMy(..)
  , Ex_
  )
  
import System.Environment ( getArgs )
import Data.List.NonEmpty( NonEmpty(..) )

  
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
  runProgram [] file >>= (putStrLn . showMy :: Ex_ -> IO ())
