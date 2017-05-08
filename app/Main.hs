module Main where

import Lib
  ( showProgram
  )

main :: IO ()
main =
  do{ args <- getArgs
    ; if null args then runRepl else runOne args
    }