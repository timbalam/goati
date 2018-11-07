module Main where

import qualified Syntax.Parser (tests)
import qualified Syntax.Expr.Dyn (tests)
import qualified Syntax.Eval.Dyn (tests)
import qualified Syntax.Eval.IO.Dyn (tests)
--import qualified Syntax.Import (tests)
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return () where
  all = test
    [ "parser" ~: Syntax.Parser.tests
    , "eval" ~: Syntax.Eval.Dyn.tests
    , "expr" ~: Syntax.Expr.Dyn.tests
    , "io" ~: Syntax.Eval.IO.Dyn.tests
--    , "import" ~: Syntax.Import.tests
    ]
  
    
