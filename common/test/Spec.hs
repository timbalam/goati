module Main where

import qualified Parser (tests)
import qualified Eval.Dyn (tests)
--import qualified Eval.IO.Dyn (tests)
--import qualified Import (tests)
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return () where
  all = test
    [ "parser" ~: Parser.tests
    , "eval" ~: Eval.Dyn.tests
    --, "io" ~: Eval.IO.Dyn.tests
    --, "import" ~: Import.tests
    ]
  
    
