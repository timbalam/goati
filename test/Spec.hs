import qualified Test.Parser as P
import qualified Types.Parser as T

import Control.Monad
  ( sequence_
  )
  
wrap x = T.Rnode [T.Eval x]

main :: IO ()
main = 
  sequence_
    [ P.testParser "\"hi\"" $ wrap (T.String "hi")
    , P.testParser "\"one\" \"two\"" $ wrap (T.String "onetwo")
    , P.testParser "123" $ wrap (T.Number 123)
    , P.testParser "123." $ wrap (T.Number 123)
    , P.testParser "123.0" $ wrap (T.Number 123)
    , P.testParser "1_000.2_5" $ wrap (T.Number 1000.25)
    , P.testParser "name" $ wrap (rident "name")
    , P.testParser "path.to.thing" $ wrap (T.Rroute (T.Rroute (rident "path" `T.Route` ref "to") `T.Route` ref "thing"))
    , P.testParser ".local" $ wrap (T.Rroute (T.Atom (ref "local")))
    , P.testParser "(bracket)" $ wrap (rident "bracket")
    , P.testParser "a.thing(applied)" $ wrap (T.Rroute (rident "a" `T.Route` ref "thing") `T.App` rident "applied")
    , P.testParser ".local(applied)" $ wrap (T.Rroute (T.Atom (ref "local")) `T.App` rident "applied")
    , P.testParser ".thing(a).get(b)" $ wrap (T.Rroute ((T.Rroute (T.Atom (ref "thing")) `T.App` rident "a") `T.Route` ref "get") `T.App` rident "b")
    , P.testParser "-45" $ wrap (T.Unop T.Neg (T.Number 45))
    , P.testParser "!hi" $ wrap (T.Unop T.Not (rident "hi"))
    , P.testParser "this & that" $ wrap (rident "this" `and` rident "that")
    , P.testParser "4 | 2" $ wrap (T.Number 4 `or` T.Number 2)
    , P.testParser "10 + 3" $ wrap (T.Number 10 `add` T.Number 3)
    , P.testParser "a + b + c" $ wrap ((rident "a" `add` rident "b") `add` rident "c")
    , P.testParser "a - b" $ wrap (rident "a" `sub`rident "b")
    , P.testParser "a + b - c" $ wrap ((rident "a" `add` rident "b") `sub` rident "c")
    , P.testParser "a * 2" $ wrap (rident "a" `prod` T.Number 2)
    , P.testParser "value / 2" $ wrap (rident "value" `div` T.Number 2)
    , P.testParser "3^i" $ wrap (T.Number 3 `pow` rident "i")
    , P.testParser "1 + 1 + 3 & 5 - 1" $ wrap (((T.Number 1 `add` T.Number 1) `add` T.Number 3) `and` (T.Number 5 `sub` T.Number 1))
    , P.testParser "1 + 1 + 3 * 5 - 1" $ wrap (((T.Number 1 `add` T.Number 1) `add` (T.Number 3 `prod` T.Number 5)) `sub` T.Number 1)
    , P.testParser "assign = 1" $ T.Rnode [lident "assign" `T.Assign` T.Number 1]
    , P.testParser "{ a = b }" $ wrap (T.Rnode [lident "a" `T.Assign` rident "b"])
    , P.testParser "{ a = 1; b = a; c }" $ wrap (T.Rnode [lident "a" `T.Assign` T.Number 1, lident "b" `T.Assign` rident "a", T.Eval (rident "c")])
    , P.testParser "{ .member = b } = object" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "member")) `T.ReversibleAssign` lident "b"] `T.Assign` rident "object"]
    , P.testParser "*b" $ T.Rnode [T.Unpack (rident "b")]
    , P.testParser "{ .x = .val; *.y } = thing" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "val")), T.ReversibleUnpack (lroute (T.Atom (ref "y")))] `T.Assign` rident "thing"]
    , P.testParser "{ *.y; .x = .out } = object" $ T.Rnode [T.Lnode [T.ReversibleUnpack (lroute (T.Atom (ref "y"))), T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "out"))] `T.Assign` rident "object"]
    , P.testParser "{ .x = .val; *y; .z = priv } = other" $ T.Rnode [T.Lnode [T.PlainRoute (T.Atom (ref "x")) `T.ReversibleAssign` lroute (T.Atom (ref "val")), T.ReversibleUnpack (lident "y"), T.PlainRoute (T.Atom (ref "z")) `T.ReversibleAssign` lident "priv"] `T.Assign` rident "other"]
    ]
    where
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
    
