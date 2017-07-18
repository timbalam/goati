module Test.Parser 
  ( tests
  ) where

import qualified Types.Parser as T
import Types.Parser.Short
import qualified Types.Error as E
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
    (assertEqual banner expected)
    (readProgram input)
  where
    banner = "Parsing \"" ++ input ++ "\""
      
assertParseError :: String -> String -> Assertion
assertParseError msg input =
  either
    (\ _ -> return ())
    (\ res -> assertFailure (banner ++ "\nexpected " ++ msg ++ " but got: " ++ show res))
    (readProgram input)
  where
    banner = "Parsing \"" ++ input ++ "\""
    
tests =
 TestList
    [ TestLabel "empty program" . TestCase $ assertParseError "empty program" ""
    , TestLabel "string" . TestCase $ assertParse "\"hi\"" (wrap (T.String "hi"))
    , TestLabel "whitespace separated strings" . TestCase $ assertParse "\"one\" \"two\"" (wrap (T.String "onetwo"))
    , TestLabel "number" . TestCase . assertParse "123" $ wrap (T.Number 123)
    , TestLabel "trailing decimal" . TestCase . assertParse "123." $ wrap (T.Number 123)
    , TestLabel "decimal with trailing digits" . TestCase . assertParse "123.0" $ wrap (T.Number 123)
    , TestLabel "underscores in number" . TestCase . assertParse "1_000.2_5" $ wrap (T.Number 1000.25)
    , TestLabel "binary" . TestCase . assertParse "0b100" $ wrap (T.Number 4)
    , TestLabel "octal" . TestCase . assertParse "0o11" $ wrap (T.Number 9)
    , TestLabel "hexidecimal" . TestCase .assertParse "0xa0" $ wrap (T.Number 160)
    , TestLabel "plain identifier" . TestCase . assertParse "name" $ wrap (rident "name")
    , TestLabel "period separated identifiers" . TestCase . assertParse "path.to.thing" $ wrap ((rident "path" `rref` "to") `rref` "thing")
    , TestLabel "identifiers separated by period and space" . TestCase . assertParse "with. space" $ wrap (rident "with" `rref` "space")
    , TestLabel "identifiers separated by space and period" . TestCase . assertParse "with .space" $ wrap (rident "with" `rref` "space")
    , TestLabel "identifiers separaed by spaces around period" . TestCase . assertParse "with . spaces" $ wrap (rident "with"`rref` "spaces")
    , TestLabel "identifier with  beginning period" . TestCase . assertParse ".local" $ wrap (rsref "local")
    , TestLabel "brackets around identifier" . TestCase . assertParse "(bracket)" $ wrap (rident "bracket")
    , TestLabel "empty brackets" . TestCase $ assertParseError "empty bracket" "()"
    , TestLabel "identifier with applied brackets" . TestCase . assertParse "a.thing(applied)" $ wrap ((rident "a" `rref` "thing") `T.App` rident "applied")
    , TestLabel "identifier beginning with period with applied brackets" . TestCase . assertParse ".local(applied)" $ wrap (rsref "local" `T.App` rident "applied")
    , TestLabel "chained applications" . TestCase . assertParse ".thing(a).get(b)" $ wrap (((rsref "thing" `T.App` rident "a") `rref` "get") `T.App` rident "b")
    , TestLabel "primitive negative number" . TestCase . assertParse "-45" $ wrap (T.Unop T.Neg (T.Number 45))
    , TestLabel "boolean not" . TestCase . assertParse "!hi" $ wrap (T.Unop T.Not (rident "hi"))
    , TestLabel "boolean and" . TestCase . assertParse "this & that" $ wrap (rident "this" `_and_` rident "that")
    , TestLabel "boolean or" . TestCase . assertParse "4 | 2" $ wrap (T.Number 4 `_or_` T.Number 2)
    , TestLabel "addition" . TestCase . assertParse "10 + 3" $ wrap (T.Number 10 `_add_` T.Number 3)
    , TestLabel "multiple additions" . TestCase . assertParse "a + b + c" $ wrap ((rident "a" `_add_` rident "b") `_add_` rident "c")
    , TestLabel "subtration" . TestCase . assertParse "a - b" $ wrap (rident "a" `_sub_`rident "b")
    , TestLabel "mixed addition and subtraction" . TestCase . assertParse "a + b - c" $ wrap ((rident "a" `_add_` rident "b") `_sub_` rident "c")
    , TestLabel "multiplication" . TestCase . assertParse "a * 2" $ wrap (rident "a" `_prod_` T.Number 2)
    , TestLabel "division" . TestCase . assertParse "value / 2" $ wrap (rident "value" `_div_` T.Number 2)
    , TestLabel "power" . TestCase . assertParse "3^i" $ wrap (T.Number 3 `_pow_` rident "i")
    , TestLabel "comparisons"
        (TestList
           [ TestCase . assertParse "3 > 2" $ wrap (T.Number 3 `_gt_` T.Number 2)
           , TestCase . assertParse "2 < abc" $ wrap (T.Number 2 `_lt_` rident "abc")
           , TestCase . assertParse "a <= b" $ wrap (rident "a" `_le_` rident "b")
           , TestCase . assertParse "b >= 4" $ wrap (rident "b" `_ge_` T.Number 4)
           , TestCase . assertParse "2 == True" $ wrap (T.Number 2 `_eq_` rident "True")
           , TestCase . assertParse "3 != 3" $ wrap (T.Number 3 `_ne_` T.Number 3)
           ])
    , TestLabel "mixed numeric and boolean operations" . TestCase . assertParse "1 + 1 + 3 & 5 - 1" $ wrap (((T.Number 1 `_add_` T.Number 1) `_add_` T.Number 3) `_and_` (T.Number 5 `_sub_` T.Number 1))
    , TestLabel "mixed addition, subtration and multiplication" . TestCase . assertParse "1 + 1 + 3 * 5 - 1" $ wrap (((T.Number 1 `_add_` T.Number 1) `_add_` (T.Number 3 `_prod_` T.Number 5)) `_sub_` T.Number 1)
    , TestLabel "assignment" . TestCase . assertParse "assign = 1" $ T.Rnode [lident "assign" `T.Assign` T.Number 1]
    , TestLabel "assign zero" . TestCase . assertParse "assign = 0" $ T.Rnode [lident "assign" `T.Assign` T.Number 0]
    , TestLabel "declare" . TestCase . assertParse "undef =" $ T.Rnode [T.Declare (lident' "undef")]
    , TestLabel "object with assignment" .  TestCase . assertParse "{ a = b }" $ wrap (T.Rnode [lident "a" `T.Assign` rident "b"])
    , TestLabel "object with multiple statements" . TestCase . assertParse "{ a = 1; b = a; c }" $ wrap (T.Rnode [lident "a" `T.Assign` T.Number 1, lident "b" `T.Assign` rident "a", T.Eval (rident "c")])
    , TestLabel "empty object" . TestCase $
        assertParse "{}" (wrap (T.Rnode []))
    , TestLabel "destructuring assignment" . TestCase $
        assertParse
          "{ .member = b } = object"
          (T.Rnode
            [ T.Lnode
                [ plainsref "member" `T.ReversibleAssign` lident "b"]
              `T.Assign` rident "object"
            ])
    , TestLabel "unpacked value" . TestCase . assertParse "*b" $ T.Rnode [T.Unpack (rident "b")]
    , TestLabel "destructuring with final unpack statement" . TestCase $
        assertParse
          "{ .x = .val; *.y } = thing"
          (T.Rnode
            [ T.Lnode
                [ plainsref "x" `T.ReversibleAssign` lsref "val"
                , T.ReversibleUnpack (lsref "y")
                ]
                `T.Assign` rident "thing"
            ])
    , TestLabel "destructuring with beginning unpack statement" . TestCase $
        assertParse
          "{ *.y; .x = .out } = object"
          (T.Rnode
            [ T.Lnode
                [ T.ReversibleUnpack (lsref "y")
                , plainsref "x" `T.ReversibleAssign` lsref "out"
                ]
              `T.Assign` rident "object"
            ])
    , TestLabel "destructuring with internal unpack statement" . TestCase $
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
