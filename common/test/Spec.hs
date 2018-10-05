module Main where

import qualified Syntax.Class.Parser (tests)
import qualified Syntax.Class.Expr (tests)
import qualified Syntax.Class.Eval (tests)
import qualified Syntax.Class.IO (tests)
--import qualified Syntax.Class.Import (tests)
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return () where
  all = test
    [ "parser" ~: Syntax.Class.Parser.tests
    , "eval" ~: Syntax.Class.Eval.tests
    , "expr" ~: Syntax.Class.Expr.tests
    , "io" ~: Syntax.Class.IO.tests
--    , "import" ~: Syntax.Class.Import.tests
    ]
  
    
