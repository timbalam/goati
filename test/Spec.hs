module Main where

import qualified Syntax.Type (tests)
import qualified Syntax.Class (tests)
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      test
        [ "type" ~: Syntax.Type.tests
        , "class" ~: Syntax.Class.tests
        ]
  
    
