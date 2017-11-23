import qualified Test.Parser.Short as PS ( tests )
import qualified Test.Parser as P ( tests )
import Test.Eval as E ( tests )
  
import Test.HUnit
  ( runTestTT
  , Test(..)
  )
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      TestList
        [ TestLabel "short" PS.tests
        , TestLabel "parser" P.tests
        , TestLabel "eval" E.tests
        ]
  
    
