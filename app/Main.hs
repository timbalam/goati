module Main where

import Lib
  ( readProgram
  )

main :: IO ()
main = getLine >>= putStr . readProgram
