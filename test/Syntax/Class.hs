module Syntax.Class (tests) where

import qualified Syntax.Class.Parser (tests)
import qualified Syntax.Class.Expr (tests)
import qualified Syntax.Class.Type (tests)
import qualified Syntax.Class.Import (tests)
  
import Test.HUnit
  
tests = 
  test
    [ "parser" ~: Syntax.Class.Parser.tests
    , "expr" ~: Syntax.Class.Expr.tests
    , "type" ~: Syntax.Class.Type.tests
    , "import" ~: Syntax.Class.Import.tests
    ]
  
    
