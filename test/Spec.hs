import qualified Test.Parser.Short as PS ( tests )
--import Test.Parser( tests as Ptests )
--import Test.Eval( tests as Etests )
  
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
        --, TestLabel "parser" Ptests
        --, TestLabel "eval" E.tests
        ]
  
    
