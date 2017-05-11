module Test.Parser 
  ( tests
  ) where

import qualified Types.Parser as T
import Types.Short
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
    [ TestLabel "empty program" . TestCase $ assertError "empty program" "" isParseError
    , TestLabel "string" . TestCase $ assertParse "\"hi\"" (wrap (T.String "hi"))
    , TestLabel "whitespace separated strings" . TestCase $ assertParse "\"one\" \"two\"" (wrap (T.String "onetwo"))
    , TestLabel "number" . TestCase . assertParse "123" $ wrap (T.Number 123)
    , TestLabel "trailing decimal" . TestCase . assertParse "123." $ wrap (T.Number 123)
    , TestLabel "decimal with trailing digits" . TestCase . assertParse "123.0" $ wrap (T.Number 123)
    , TestLabel "underscores in number" . TestCase . assertParse "1_000.2_5" $ wrap (T.Number 1000.25)
    , TestLabel "plain identifier" . TestCase . assertParse "name" $ wrap (rident "name")
    , TestLabel "period separated identifiers" . TestCase . assertParse "path.to.thing" $ wrap ((rident "path" `rref` "to") `rref` "thing")
    , TestLabel "identifier with  beginning period" . TestCase . assertParse ".local" $ wrap (rsref "local")
    , TestLabel "brackets around identifier" . TestCase . assertParse "(bracket)" $ wrap (rident "bracket")
    , TestLabel "empty brackets" . TestCase $ assertError "empty bracket" "()" isParseError
    , TestLabel "identifier with applied brackets" . TestCase . assertParse "a.thing(applied)" $ wrap ((rident "a" `rref` "thing") `T.App` rident "applied")
    , TestLabel "identifier beginning with period with applied brackets" . TestCase . assertParse ".local(applied)" $ wrap (rsref "local" `T.App` rident "applied")
    , TestCase . assertParse ".thing(a).get(b)" $ wrap (((rsref "thing" `T.App` rident "a") `rref` "get") `T.App` rident "b")
    , TestCase . assertParse "-45" $ wrap (T.Unop T.Neg (T.Number 45))
    , TestCase . assertParse "!hi" $ wrap (T.Unop T.Not (rident "hi"))
    , TestCase . assertParse "this & that" $ wrap (rident "this" `_and_` rident "that")
    , TestCase . assertParse "4 | 2" $ wrap (T.Number 4 `_or_` T.Number 2)
    , TestCase . assertParse "10 + 3" $ wrap (T.Number 10 `_add_` T.Number 3)
    , TestCase . assertParse "a + b + c" $ wrap ((rident "a" `_add_` rident "b") `_add_` rident "c")
    , TestCase . assertParse "a - b" $ wrap (rident "a" `_sub_`rident "b")
    , TestCase . assertParse "a + b - c" $ wrap ((rident "a" `_add_` rident "b") `_sub_` rident "c")
    , TestCase . assertParse "a * 2" $ wrap (rident "a" `_prod_` T.Number 2)
    , TestCase . assertParse "value / 2" $ wrap (rident "value" `_div_` T.Number 2)
    , TestCase . assertParse "3^i" $ wrap (T.Number 3 `_pow_` rident "i")
    , TestCase . assertParse "1 + 1 + 3 & 5 - 1" $ wrap (((T.Number 1 `_add_` T.Number 1) `_add_` T.Number 3) `_and_` (T.Number 5 `_sub_` T.Number 1))
    , TestCase . assertParse "1 + 1 + 3 * 5 - 1" $ wrap (((T.Number 1 `_add_` T.Number 1) `_add_` (T.Number 3 `_prod_` T.Number 5)) `_sub_` T.Number 1)
    , TestCase . assertParse "assign = 1" $ T.Rnode [lident "assign" `T.Assign` T.Number 1]
    , TestCase . assertParse "undef =" $ T.Rnode [T.Declare (lident' "undef")]
    , TestCase . assertParse "{ a = b }" $ wrap (T.Rnode [lident "a" `T.Assign` rident "b"])
    , TestCase . assertParse "{ a = 1; b = a; c }" $ wrap (T.Rnode [lident "a" `T.Assign` T.Number 1, lident "b" `T.Assign` rident "a", T.Eval (rident "c")])
    , TestCase $
        assertParse
          "{ .member = b } = object"
          (T.Rnode
            [ T.Lnode
                [ plainsref "member" `T.ReversibleAssign` lident "b"]
              `T.Assign` rident "object"
            ])
    , TestCase . assertParse "*b" $ T.Rnode [T.Unpack (rident "b")]
    , TestCase $
        assertParse
          "{ .x = .val; *.y } = thing"
          (T.Rnode
            [ T.Lnode
                [ plainsref "x" `T.ReversibleAssign` lsref "val"
                , T.ReversibleUnpack (lsref "y")
                ]
                `T.Assign` rident "thing"
            ])
    , TestCase $
        assertParse
          "{ *.y; .x = .out } = object"
          (T.Rnode
            [ T.Lnode
                [ T.ReversibleUnpack (lsref "y")
                , plainsref "x" `T.ReversibleAssign` lsref "out"
                ]
              `T.Assign` rident "object"
            ])
    , TestCase $
        assertParse
          "{ .x = .val; *y; .z = priv } = other"
          (T.Rnode
            [ T.Lnode
                [ plainsref "x" `T.ReversibleAssign` lsref "val"
                , T.ReversibleUnpack (lident "y")
                , plainsref "z" `T.ReversibleAssign` lident "priv"
                ]
              `T.Assign` rident "other"
            ])
    ]
    where
      wrap x = T.Rnode [T.Eval x]
