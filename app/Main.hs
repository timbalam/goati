module Main where


import Version( myiReplVersion )
import Lib
  ( runProgram
  , browse
  , ShowMy(..)
  , Expr
  , Vid
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
runRepl = browse

    
runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  runProgram [] file >>= (putStrLn . showMy :: Expr Vid -> IO ())
