module Main where

import qualified Syntax.Class (tests)
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      test Syntax.Class.tests
  
    
