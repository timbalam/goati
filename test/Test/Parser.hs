module Test.Parser 
  ( tests
  ) where

import qualified Types.Parser as T
import qualified Error as E
import Lib
  ( readProgram
  )

import Test.HUnit
  ( Test(..)
  , Assertion(..)
  , assertEqual
  , assertFailure
  , assertBool
  )
 
assertParse :: String -> T.Rval -> Assertion 
assertParse input expected =
  either
    (assertFailure . show)
    (\ res -> assertEqual banner res expected)
    (readProgram input)
  where
    banner = "Parsing \"" ++ input ++ "\""
      
assertError :: String -> String -> (E.Error -> Bool) -> Assertion
assertError msg input test =
  either
    (assertBool banner . test)
    (\res -> assertFailure $ banner ++ "\nexpected " ++ msg ++ " but got: " ++ show res)
    (readProgram input)
  where
    banner = "Parsing \"" ++ input ++ "\""

isParseError :: E.Error -> Bool
isParseError (E.Parser _ _) = True
isParseError _ = False
    
tests =
 TestList
    [ TestCase $ assertError "empty program" "" isParseError
    , TestCase . assertParse "\"hi\"" $ wrap (T.String "hi")
    , TestCase . assertParse "\"one\" \"two\"" $ wrap (T.String "onetwo")
    , TestCase . assertParse "123" $ wrap (T.Number 123)
    , TestCase . assertParse "123." $ wrap (T.Number 123)
    , TestCase . assertParse "123.0" $ wrap (T.Number 123)
    , TestCase . assertParse "1_000.2_5" $ wrap (T.Number 1000.25)
    , TestCase . assertParse "name" $ wrap (rident "name")
    , TestCase . assertParse "path.to.thing" $ wrap (T.Rroute (T.Rroute (rident "path" `T.Route` ref "to") `T.Route` ref "thing"))
    , TestCase . assertParse ".local" $ wrap (T.Rroute (T.Atom (ref "local")))
    , TestCase . assertParse "(bracket)" $ wrap (rident "bracket")
    , TestCase $ assertError "empty bracket" "()" isParseError
    , TestCase . assertParse "a.thing(applied)" $ wrap (T.Rroute (rident "a" `T.Route` ref "thing") `T.App` rident "applied")
    , TestCase . assertParse ".local(applied)" $ wrap (T.Rroute (T.Atom (ref "local")) `T.App` rident "applied")
    , TestCase . assertParse ".thing(a).get(b)" $ wrap (T.Rroute ((T.Rroute (T.Atom (ref "thing")) `T.App` rident "a") `T.Route` ref "get") `T.App` rident "b")
    , TestCase . assertParse "-45" $ wrap (T.Unop T.Neg (T.Number 45))
    , TestCase . assertParse "!hi" $ wrap (T.Unop T.Not (rident "hi"))
    , TestCase . assertParse "this & that" $ wrap (rident "this" `and` rident "that")
    , TestCase . assertParse "4 | 2" $ wrap (T.Number 4 `or` T.Number 2)
    , TestCase . assertParse "10 + 3" $ wrap (T.Number 10 `add` T.Number 3)
    , TestCase . assertParse "a + b + c" $ wrap ((rident "a" `add` rident "b") `add` rident "c")
    , TestCase . assertParse "a - b" $ wrap (rident "a" `sub`rident "b")
    , TestCase . assertParse "a + b - c" $ wrap ((rident "a" `add` rident "b") `sub` rident "c")
    , TestCase . assertParse "a * 2" $ wrap (rident "a" `prod` T.Number 2)
    , TestCase . assertParse "value / 2" $ wrap (rident "value" `div` T.Number 2)
    , TestCase . assertParse "3^i" $ wrap (T.Number 3 `pow` rident "i")
    , TestCase . assertParse "1 + 1 + 3 & 5 - 1" $ wrap (((T.Number 1 `add` T.Number 1) `add` T.Number 3) `and` (T.Number 5 `sub` T.Number 1))
    , TestCase . assertParse "1 + 1 + 3 * 5 - 1" $ wrap (((T.Number 1 `add` T.Number 1) `add` (T.Number 3 `prod` T.Number 5)) `sub` T.Number 1)
    , TestCase . assertParse "assign = 1" $ T.Rnode [lident "assign" `T.Assign` T.Number 1]
    , TestCase . assertParse "undef =" $ T.Rnode [lident "undef" `T.Assign` T.Undef]
    , TestCase . assertParse "{ a = b }" $ wrap (T.Rnode [lident "a" `T.Assign` rident "b"])
    , TestCase . assertParse "{ a = 1; b = a; c }" $ wrap (T.Rnode [lident "a" `T.Assign` T.Number 1, lident "b" `T.Assign` rident "a", T.Eval (rident "c")])
    , TestCase . assertParse "{ .member = b } = object" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "member")) `T.ReversibleAssign` lident "b"] `T.Assign` rident "object"]
    , TestCase . assertParse "*b" $ T.Rnode [T.Unpack (rident "b")]
    , TestCase . assertParse "{ .x = .val; *.y } = thing" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "val")), T.ReversibleUnpack (lroute (T.Atom (ref "y")))] `T.Assign` rident "thing"]
    , TestCase . assertParse "{ *.y; .x = .out } = object" $ T.Rnode [T.Lnode [T.ReversibleUnpack (lroute (T.Atom (ref "y"))), T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "out"))] `T.Assign` rident "object"]
    , TestCase . assertParse "{ .x = .val; *y; .z = priv } = other" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "val")), T.ReversibleUnpack (lident "y"), T.PlainRoute (T.Atom (ref "z")) `T.ReversibleAssign` lident "priv"] `T.Assign` rident "other"]
    ]
    where
      wrap x = T.Rnode [T.Eval x]
      ref = T.Ref . T.Ident
      rident = T.Rident . T.Ident
      and = T.Binop T.And
      or = T.Binop T.Or
      add = T.Binop T.Add
      sub = T.Binop T.Sub
      prod = T.Binop T.Prod
      div = T.Binop T.Div
      pow = T.Binop T.Pow
      lident = T.Laddress . T.Lident . T.Ident
      lroute = T.Laddress . T.Lroute
