module Test where

import Lib
  ( readProgram
  )
  
runTests :: IO ()
runTests = (\a -> do{ putStrLn (">" ++ a); putStrLn (readProgram a) }) `mapM_` tests
  where
    tests = 
      [ "\"hi\"" -- string
      , "\"one\" \"two\"" -- string
      , "123" -- integer
      , "123." -- float
      , "123.0" -- float
      , "1_000.2_5" -- float
      , "name" -- identifier
      , "path.to.thing" -- route
      , ".local" -- local route
      , "(bracketTest)" -- bracket
      , "a.thing(applied)" -- application
      , ".local(applied)" -- local application
      , ".thing(a).get(b)" -- get application
      , "-45" -- negate operation
      , "!hi" -- logical negate operation
      , "this & that" -- and operation
      , "4 | 2" -- or operation
      , "10 + 3" -- add operation
      , "a - b" -- sub operation
      , "a * 2" -- mul operation
      , "value / 2" -- div operation
      , "3^i" -- pow expr
      ]