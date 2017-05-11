module Main where

import System.Environment ( getArgs )
import Data.List.NonEmpty ( NonEmpty(..) )
import Lib
  ( runRepl
  , runOne
  )

main :: IO ()
main =
  do{ args <- getArgs
    ; case args of [] -> runRepl; (file:args) -> runOne (file:|args)
    }