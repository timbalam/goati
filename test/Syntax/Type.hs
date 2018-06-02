module Syntax.Type (tests) where

import qualified Syntax.Type.Parser (tests)
import qualified Syntax.Type.Expr (tests)
import qualified Syntax.Type.Parser.Short (tests)
import qualified Syntax.Type.Import (tests)
import qualified Syntax.Type.Eval (tests)
import qualified Syntax.Type.IO (tests)
  
import Test.HUnit
  
tests = 
  test
    [ "short" ~: Syntax.Type.Parser.Short.tests
    , "parser" ~: Syntax.Type.Parser.tests
    , "expr" ~: Syntax.Type.Expr.tests
    , "import" ~: Syntax.Type.Import.tests
    , "eval" ~: Syntax.Type.Eval.tests
    , "io" ~: Syntax.Type.IO.tests
    ]
  
    
