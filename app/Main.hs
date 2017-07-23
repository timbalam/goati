module Main where

import Lib
  ( runRepl
  , runOne
  )
  
import System.Environment ( getArgs )
import Data.List.NonEmpty ( NonEmpty(..) )

  
main :: IO ()
main =
  do
    args <- getArgs
    case args of
      [] -> runRepl
      (file:args) -> runOne (file:|args)
