import qualified Test.Parser.Short as PS ( tests )
import qualified Test.Parser as P ( tests )
import qualified Test.Core as C ( tests )
import qualified Test.Eval as E ( tests )
  
import Test.HUnit
  ( runTestTT
  , Test(..)
  )
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      TestList [
        --TestLabel "short" PS.tests,
        --TestLabel "parser" P.tests,
        --TestLabel "core" C.tests
        --, TestLabel "eval" E.tests
        ]
  
    
