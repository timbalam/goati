module Main where

import Lib
  ( showProgram
  )

main :: IO ()
main = getLine >>= putStr . showProgram
