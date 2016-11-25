import qualified Test.Parser as P
  ( tests
  )
import qualified Test.Eval as E
  ( tests
  )
  
import Test.HUnit
  ( runTestTT
  , Test(..)
  )
  

main :: IO ()
main = runTestTT all >> return ()
  where
    all =
      TestList
        [ TestLabel "parser" P.tests
        , TestLabel "eval" E.tests
        ]
  
    
