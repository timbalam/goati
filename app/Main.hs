module Main where

import Lib
  ( readProgram
  )

main :: IO ()
main = putStrLn . readProgram
