module Main where

import Parser.Short (shortTests)
import Parser (parserTests)
import Expr (exprTests)
import Import (importTests)
import Eval (evalTests)
import IO (ioTests)
import qualified Syntax.Parser (tests)
import qualified Syntax.Expr (tests)
import qualified Syntax.Class (tests)
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      test
        [
        -- "short" ~: shortTests
        --, "parser" ~: parserTests
        --, "expr" ~: exprTests
        --, "import" ~: importTests
        --, "eval" ~: evalTests
        --, "io" ~: ioTests
        --, 
        "syntax" ~:
          [ "parser" ~: Syntax.Parser.tests
          , "expr" ~: Syntax.Expr.tests
          , "class" ~: Syntax.Class.tests
          ]
        ]
  
    
