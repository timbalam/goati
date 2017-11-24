import qualified Test.Parser.Short as Short ( tests )
import qualified Test.Parser as Parser ( tests )
import qualified Test.Core as Core ( tests )
import qualified Test.Eval as Eval ( tests )
  
import Test.HUnit
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      test
        [ --TestLabel "short" Short.tests
        --, TestLabel "parser" Parser.tests
        --,
        "core" ~: Core.tests
        --, TestLabel "eval" Eval.tests
        ]
  
    
