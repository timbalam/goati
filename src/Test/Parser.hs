module Test.Parser where

import qualified Types.Parser as T
import Lib
  ( readProgram
  , showProgram
  )
  
assertFailure :: String -> IO ()
assertFailure msg = ioError (userError ("Test:" ++ msg))

assertParserFailure :: String -> IO ()
assertParserFailure msg = assertFailure ("Parsing \"" ++ msg ++ "\"")

testParser :: String -> T.Rval -> IO ()
testParser input expected =
  case
    readProgram input
  of
    Right x | x == expected -> return ()
    _ -> assertParserFailure input

runTests :: IO ()
runTests = (\a -> do{ putStrLn (">" ++ a); putStrLn (showProgram a) }) `mapM_` tests
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
      , "a + b + c"
      , "a - b" -- sub operation
      , "a + b - c"
      , "a * 2" -- mul operation
      , "value / 2" -- div operation
      , "3^i" -- pow operation
      , "1 + 1 + 3 & 5 - 1" -- arithmetic expression
      , "1 + 1 + 3 * 5 - 1"
      , "assign = 1" -- assignment
      , "{ a = b }" -- node
      , "{ a = 1; b = a; c }" -- multiple statements
      , "{ .member = b } = object" -- destructuring assignment
      , "*b" -- unpack statement
      , "{ .x = .val; *.y } = thing" -- destructure and unpack
      , "{ *.y; .x = .out } = object" -- unpack and destructure
      , "{ .x = .val; *y; .z = priv } = other" 
      ]