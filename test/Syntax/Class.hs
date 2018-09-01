module Syntax.Class (tests) where

import qualified Syntax.Class.Parser (tests)
import qualified Syntax.Class.Type (tests)
import qualified Syntax.Class.Eval (tests)
--import qualified Syntax.Class.IO (tests)
--import qualified Syntax.Class.Import (tests)
  
import Test.HUnit
  
tests = 
  test
    [-- "parser" ~: Syntax.Class.Parser.tests
--    , "type" ~: Syntax.Class.Type.tests
--    , 
    "eval" ~: Syntax.Class.Eval.tests
--    , "io" ~: Syntax.Class.IO.tests
--    , "import" ~: Syntax.Class.Import.tests
    ]
  
    
