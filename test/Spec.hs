import qualified Test.Parser.Short as Short ( tests )
import qualified Test.Parser as Parser ( tests )
import qualified Test.Expr as Expr ( tests )
import qualified Test.Import as Import( tests )
import qualified Test.Eval as Eval ( tests )
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      test
        [-- "short" ~: Short.tests
        --, "parser" ~: Parser.tests
        --,
        "expr" ~: Expr.tests
        --, "import" ~: Import.tests
        --, "eval" ~: Eval.tests
        ]
  
    
