module Test.Parser 
  ( parserTest
  , tests
  ) where

import qualified Types.Parser as T
import Lib
  ( readProgram
  )

import Test.HUnit
  ( Test(..)
  , assertEqual
  , assertFailure
  )
 
parserTest :: String -> T.Rval -> Test 
parserTest input expected =
  TestCase $
    case
      readProgram input
    of
      Right x -> assertEqual ("Parsing \"" ++ input ++ "\"") x expected
      Left e -> assertFailure $ show e

tests =
 TestList
    [ parserTest "\"hi\"" $ wrap (T.String "hi")
    , parserTest "\"one\" \"two\"" $ wrap (T.String "onetwo")
    , parserTest "123" $ wrap (T.Number 123)
    , parserTest "123." $ wrap (T.Number 123)
    , parserTest "123.0" $ wrap (T.Number 123)
    , parserTest "1_000.2_5" $ wrap (T.Number 1000.25)
    , parserTest "name" $ wrap (rident "name")
    , parserTest "path.to.thing" $ wrap (T.Rroute (T.Rroute (rident "path" `T.Route` ref "to") `T.Route` ref "thing"))
    , parserTest ".local" $ wrap (T.Rroute (T.Atom (ref "local")))
    , parserTest "(bracket)" $ wrap (rident "bracket")
    , parserTest "a.thing(applied)" $ wrap (T.Rroute (rident "a" `T.Route` ref "thing") `T.App` rident "applied")
    , parserTest ".local(applied)" $ wrap (T.Rroute (T.Atom (ref "local")) `T.App` rident "applied")
    , parserTest ".thing(a).get(b)" $ wrap (T.Rroute ((T.Rroute (T.Atom (ref "thing")) `T.App` rident "a") `T.Route` ref "get") `T.App` rident "b")
    , parserTest "-45" $ wrap (T.Unop T.Neg (T.Number 45))
    , parserTest "!hi" $ wrap (T.Unop T.Not (rident "hi"))
    , parserTest "this & that" $ wrap (rident "this" `and` rident "that")
    , parserTest "4 | 2" $ wrap (T.Number 4 `or` T.Number 2)
    , parserTest "10 + 3" $ wrap (T.Number 10 `add` T.Number 3)
    , parserTest "a + b + c" $ wrap ((rident "a" `add` rident "b") `add` rident "c")
    , parserTest "a - b" $ wrap (rident "a" `sub`rident "b")
    , parserTest "a + b - c" $ wrap ((rident "a" `add` rident "b") `sub` rident "c")
    , parserTest "a * 2" $ wrap (rident "a" `prod` T.Number 2)
    , parserTest "value / 2" $ wrap (rident "value" `div` T.Number 2)
    , parserTest "3^i" $ wrap (T.Number 3 `pow` rident "i")
    , parserTest "1 + 1 + 3 & 5 - 1" $ wrap (((T.Number 1 `add` T.Number 1) `add` T.Number 3) `and` (T.Number 5 `sub` T.Number 1))
    , parserTest "1 + 1 + 3 * 5 - 1" $ wrap (((T.Number 1 `add` T.Number 1) `add` (T.Number 3 `prod` T.Number 5)) `sub` T.Number 1)
    , parserTest "assign = 1" $ T.Rnode [lident "assign" `T.Assign` T.Number 1]
    , parserTest "{ a = b }" $ wrap (T.Rnode [lident "a" `T.Assign` rident "b"])
    , parserTest "{ a = 1; b = a; c }" $ wrap (T.Rnode [lident "a" `T.Assign` T.Number 1, lident "b" `T.Assign` rident "a", T.Eval (rident "c")])
    , parserTest "{ .member = b } = object" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "member")) `T.ReversibleAssign` lident "b"] `T.Assign` rident "object"]
    , parserTest "*b" $ T.Rnode [T.Unpack (rident "b")]
    , parserTest "{ .x = .val; *.y } = thing" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "val")), T.ReversibleUnpack (lroute (T.Atom (ref "y")))] `T.Assign` rident "thing"]
    , parserTest "{ *.y; .x = .out } = object" $ T.Rnode [T.Lnode [T.ReversibleUnpack (lroute (T.Atom (ref "y"))), T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "out"))] `T.Assign` rident "object"]
    , parserTest "{ .x = .val; *y; .z = priv } = other" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "val")), T.ReversibleUnpack (lident "y"), T.PlainRoute (T.Atom (ref "z")) `T.ReversibleAssign` lident "priv"] `T.Assign` rident "other"]
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
