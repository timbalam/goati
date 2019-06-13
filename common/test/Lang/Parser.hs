{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts, OverloadedLists #-}
module Lang.Parser (tests) where

import Goat.Lang.Class
import Goat.Lang.Parser
  (parse, tokens, Parser, showToken)
import Data.Text (Text)
import Test.HUnit

banner :: Show a => a -> String
banner a = "For " ++ shows a ","

parses :: Parser a -> Text -> IO a
parses parser input =
  either
    (ioError . userError . show)
    return
    (parse tokens "test" input >>= parse parser "test")

fails :: Show a => Parser a -> Text -> Assertion
fails parser input =
  either
    (return . const ())
    (ioError . userError . show)
    (parse tokens "test" input >>= parse parser "test")

tests
  :: ( Eq a, Show a, Definition_ a
     , Eq b, Show b, ProgBlock_ b, Definition_ (Rhs (Item b))
     )
  => Parser a -> Parser b -> Test
tests rhs program =
  TestList
    [ "empty program"  ~: emptyProgram program
    , "literals" ~: literals rhs
    , "expression" ~: expression rhs
    , "operators" ~: operators rhs
    , "comparisons" ~: comparisons rhs
    , "precedence" ~: precedence rhs
    , "comment" ~: comment rhs
    , "use" ~: use rhs
    , "statements" ~: statements program
    , "block" ~: block rhs
    --, "escape" ~: escape rhs
    , "extension" ~: extension rhs
    , "patterns" ~: patterns program
    ]

emptyProgram
 :: (Eq a, Show a, ProgBlock_ a) => Parser a -> Assertion
emptyProgram program = let
  r = ""
  e = []
  in parses program r >>= assertEqual (banner r) e

literals
 :: (Eq a, Show a, NumLiteral_ a, TextLiteral_ a)
 => Parser a -> Test
literals rhs = TestList
  [ "text" ~: let
      r = "\"hi\""
      e = quote_ "hi"
      in parses rhs r >>= assertEqual (banner r) e

  , "integer" ~: let
      r = "123"
      e = 123
      in parses rhs r >>= assertEqual (banner r) e

  , "trailing decimal" ~: let
      r = "123."
      e = 123.0
      in parses rhs r >>= assertEqual (banner r) e
  
  , "decimal with trailing digits" ~: let
      r = "123.0"
      e = 123.0
      in parses rhs r >>= assertEqual (banner r) e
      
  , "underscores in number" ~: let
      r = "1_000.2_5"
      e = 1000.25
      in parses rhs r >>= assertEqual (banner r) e
      
  , "binary" ~: let
      r = "0b100"
      e = 4
      in parses rhs r >>= assertEqual (banner r) e
      
  , "octal" ~: let
      r = "0o11"
      e = 9
      in parses rhs r >>= assertEqual (banner r) e
      
  , "hexidecimal" ~: let
      r = "0xa0"
      e = 160
      in parses rhs r >>= assertEqual (banner r) e
      
  ]

expression
 :: (Eq a, Show a, Definition_ a) => Parser a -> Test
expression rhs = TestList
  [ "plain identifier" ~: let
      r = "name"
      e = "name"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "period separated identifiers" ~: let
      r = "path.to.thing"
      e = "path" #. "to" #. "thing"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "identifiers separated by period and space" ~: let
      r = "with. space"
      e = "with" #. "space"
      in parses rhs r >>= assertEqual (banner r) e
              
  , "identifiers separated by space and period" ~: let
      r = "with .space"
      e = "with" #. "space"
      in parses rhs r >>= assertEqual (banner r) e
              
  , "identifiers separated by spaces around period" ~: let
      r = "with . spaces"
      e = "with" #. "spaces"
      in parses rhs r >>= assertEqual (banner r) e
          
  , "identifier with beginning period" ~: let
      r = ".local"
      e = "" #. "local"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "brackets around identifier" ~: let
      r = "(bracket)"
      e = "bracket" 
      in parses rhs r >>= assertEqual (banner r) e
        
  , "empty brackets not allowed" ~:
      fails rhs "()"
      
  , "parenthesised path" ~: let
      r = "(.path . path)"
      e = "" #. "path" #. "path"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "parenthesised literal number" ~: let
      r = "(7)"
      e = 7
      in parses rhs r >>= assertEqual (banner r) e
      
  , "parenthesised literal string" ~: let
      r = "( \"hi, there\" )"
      e = quote_ "hi, there"
      in parses rhs r >>= assertEqual (banner r) e
      
  ]


operators
 :: (Eq a, Show a, Definition_ a) => Parser a -> Test
operators rhs = TestList
  [ "primitive negative number" ~: let
      r = "-45" 
      e = neg_ 45
      in parses rhs r >>= assertEqual (banner r) e
  
  , "boolean not" ~: let
      r = "!hi" 
      e = not_ ("hi")
      in parses rhs r >>= assertEqual (banner r) e
  
  , "boolean and" ~: let
      r = "this && that"
      e = "this" #&& "that"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "boolean or" ~: let
      r = "4 || 2" 
      e = 4 #|| 2
      in parses rhs r >>= assertEqual (banner r) e
  
  , "addition" ~: let
      r = "10 + 3"
      e = 10 #+ 3
      in parses rhs r >>= assertEqual (banner r) e
  
  , "multiple additions" ~: let
      r = "a + b + c"
      e1 = "a" #+ "b" #+ "c"
      e2 = ("a" #+ "b") #+ "c"
      in do
        parses rhs r >>= assertEqual (banner r) e1
        parses rhs r >>= assertEqual (banner r) e2
  
  , "subtraction" ~: let
      r = "a - b"
      e = "a" #- "b"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "mixed addition and subtraction" ~: let
      r = "a + b - c"
      e1 = "a" #+ "b" #- "c"
      e2 = ("a" #+ "b") #- "c"
      in do
        parses rhs r >>= assertEqual (banner r) e1
        parses rhs r >>= assertEqual (banner r) e2
  
  , "multiplication" ~: let
      r = "a * 2" 
      e = "a" #* 2
      in parses rhs r >>= assertEqual (banner r) e
  
  , "division" ~: let
      r = "value / 2"
      e = "value" #/ 2
      in parses rhs r >>= assertEqual (banner r) e
  
  , "power" ~: let
      r = "3^i"
      e = 3 #^ "i"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "parenthesised addition" ~: let
      r = "(a + b)"
      e = "a" #+ "b"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "mixed operations with parentheses" ~: let
      r = "a + (b - 2)"
      e = "a" #+ ("b" #- 2)
      in parses rhs r >>= assertEqual (banner r) e

  ]
   
comparisons
 :: (Eq a, Show a, Definition_ a) => Parser a -> Test
comparisons rhs = TestList
  [ "greater than" ~: let
      r = "3 > 2" 
      e = 3 #> 2
      in parses rhs r >>= assertEqual (banner r) e
          
  , "less than" ~: let
      r = "2 < abc"
      e = 2 #< "abc"
      in parses rhs r >>= assertEqual (banner r) e
        
  , "less or equal" ~: let
      r = "a <= b"
      e = "a" #<= "b"
      in parses rhs r >>= assertEqual (banner r) e
          
  , "greater or equal" ~: let
      r = "b >= 4"
      e = "b" #>= 4
      in parses rhs r >>= assertEqual (banner r) e
          
  , "equal" ~: let
      r = "2 == True"
      e = 2 #== "True"
      in parses rhs r >>= assertEqual (banner r) e
          
  , "not equal" ~: let
      r = "3 != 3"
      e = 3 #!= 3
      in parses rhs r >>= assertEqual (banner r) e
          
  ]
    
precedence
 :: (Eq a, Show a, NumLiteral_ a, Operator_ a, Identifier_ a)
 => Parser a -> Test
precedence rhs = TestList
  [ "addition and subtraction" ~: let
      r = "1 + 1 - 3 + 5 - 1"
      e1 = 1 #+ 1 #- 3 #+ 5 #- 1
      e2 = ((((1 #+ 1) #- 3) #+ 5) #- 1)
      in do
        parses rhs r >>= assertEqual (banner r) e1
        parses rhs r >>= assertEqual (banner r) e2
  
  , "addition, subtration and multiplication" ~: let
      r = "1 + 1 + 3 * 5 - 1"
      e1 = 1 #+ 1 #+ 3 #* 5 #- 1
      e2 = ((1 #+ 1) #+ (3 #* 5)) #- 1
      in do
        parses rhs r >>= assertEqual (banner r) e1
        parses rhs r >>= assertEqual (banner r) e2
    
  , "tower of precedence" ~: let
      r = "a + b * c - d < 12 || 22 ^ e + 9 == 1 && x / 2"
      e1 = "a" #+ "b" #* "c" #- "d" #< 12 #|| 22 #^ "e" #+ 9 #== 1 #&& "x" #/ 2
      e2 = ((("a" #+ ("b" #* "c")) #- "d") #< 12) #|| ((((22 #^ "e") #+ 9) #== 1) #&& ("x" #/ 2))
      in do
        parses rhs r >>= assertEqual (banner r) e1
        parses rhs r >>= assertEqual (banner r) e2
  
  ]


comment
 :: (Eq a, Show a, NumLiteral_ a) => Parser a -> Assertion
comment rhs = let 
  r = "1 // don't parse this"
  e = 1
  in parses rhs r >>= assertEqual (banner r) e


use :: (Eq a, Show a, Definition_ a) => Parser a -> Test
use rhs = TestList
  [ "use imported name" ~: let
      r = "@use name"
      e = use_ "name"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "use has precedence over path" ~: let
      r = "@use name.get"
      e = use_ "name" #. "get"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "use has precedence over binary operator" ~: let
      r = "2 + @use name"
      e = 2 #+ use_ "name"
      in parses rhs r >>= assertEqual (banner r) e
      
  ]   

 
statements
  :: (Eq a, Show a, ProgBlock_ a, Definition_ (Rhs (Item a)))
  => Parser a -> Test
statements program = TestList
  [ "assignment" ~: let
        r = "assign = 1" 
        e = ["assign" #= 1]
        in parses program r >>= assertEqual (banner r) e
      
  , "program begins with comment" ~: let
      r = "// comment\na = b"
      e = ["a" #= "b"]
      in parses program r >>= assertEqual (banner r) e
      
  , "program contains a comment" ~: let
      r = "a = b;\n// comment line"
      e = ["a" #= "b"]
      in parses program r >>= assertEqual (banner r) e
      
  ]

block
  :: (Eq a, Show a, Definition_ a) => Parser a -> Test
block rhs = TestList
  [ "rec block with assignment" ~: let
      r = "{ a = b }"
      e = [ "a" #= "b" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "rec block with public assignment" ~: let
      r = "{ .a = b }"
      e = [ "" #. "a" #= "b" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "rec block with punned assignment" ~: let
      r = "{ .c }"
      e = [ "" #. "c" ]
      in parses rhs r >>= assertEqual (banner r) e
  
  , "rec block with punned private assignment" ~: let
      r = "{ c }"
      e = [ "c" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "rec block trailing semi-colon" ~: let
      r = "{ a = 1; }"
      e = [ "a" #= 1 ]
      in parses rhs r >>= assertEqual (banner r) e
                 
  , "rec block with multiple statements" ~: let
      r = "{ a = 1; b = a; .c }"
      e =
        [ "a" #= 1
        , "b" #= "a"
        , "" #. "c"
        ]
      in parses rhs r >>= assertEqual (banner r) e
        
  , "empty object" ~: let
      r = "{}"
      e = []
      in parses rhs r >>= assertEqual (banner r) e
      
  , "block with self reference" ~: let
      r = "{ a = a }"
      e = [ "a" #= "a" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  ]

{-
escape :: (Eq a, Show a, Expr a) => Parser a -> Test
escape rhs = TestList
  [ "block with escaped definition" ~: let
      r = "{ .a = ^b }"
      e = [ "" #. "a" #= esc_ ("b") ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "block with mixed escaped and unescaped definitions" ~: let
      r = "{ .a = 1; .b = ^a; ^c }"
      e = block_
        [ "" #. "a" #= 1
        , "" #. "b" #= esc_ ("a")
        , esc_ ("c")
        ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "single pun statement" ~: let
      r = "{ ^.a.b }"
      e = [ esc_ ("" #. "a" #. "b") ]
      in parses rhs r >>= assertEqual (banner r) e
      
  ]
-}

extension
  :: (Eq a, Show a, Definition_ a) => Parser a -> Test
extension rhs = TestList
  [ "identifier with extension" ~: let
      r = "a.thing{ .f = b }"
      e = "a" #. "thing" # [ "" #. "f" #= "b" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "identifier and extension separated by space" ~: let
      r = "a.thing { .f = b }"
      e = "a" #. "thing" # [ "" #. "f" #= "b" ]
      in parses rhs r >>= assertEqual (banner r) e
           
  , "identifier beginning with period with extension" ~: let
      r = ".local {.f = update}"
      e = "" #. "local" # [ "" #. "f" #= "update" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "extension with public pun" ~: let
      r = "a.thing { .f }"
      e = "a" #. "thing" # [ "" #. "f" ]
      in
      parses rhs r >>= assertEqual (banner r) e
           
  , "chained extensions" ~: let
      r = ".thing { .f = \"a\" }.get { .with = b }"
      e = "" #. "thing" # [ "" #. "f" #= quote_ "a" ]
        #. "get" # [ "" #. "with" #= "b" ]
      in parses rhs r >>= assertEqual (banner r) e
  ]

patterns 
 :: (Eq a, Show a, ProgBlock_ a, Definition_ (Rhs (Item a)))
 => Parser a -> Test
patterns program = TestList
  [ "destructuring assignment" ~: let
      r = "{ .member = b } = object"
      e = [[ "" #. "member" #= "b" ] #= "object"]
      in parses program r >>= assertEqual (banner r) e
      
  , "destructuring pun" ~: let
      r = "{ .member } = object"
      e = [[ "" #. "member" ] #= "object"]
      in
      parses program r >>= assertEqual (banner r) e
  {-
  , "destructuring assignment needs escaping" ~:
      fails program "{ .member = b } = object"
      
  , "destructuring pun needs escaping" ~:
      fails program "{ .member } = object"
  -}
  , "destructuring and unpacking statement" ~: let
      r = "rest { .x = .val } = thing"
      e = ["rest" # [ "" #. "x" #= "" #. "val" ] #= "thing"]
      in parses program r >>= assertEqual (banner r) e
      
  , "only unpacking statement" ~: let
      r = "rest {} = thing"
      e = ["rest" # [] #= "thing"]
      in parses program r >>= assertEqual (banner r) e
          
  , "destructuring with multiple statements" ~: let
      r = "{ .x = .val; .z = priv } = other"
      e = [
        [ "" #. "x" #= "" #. "val"
        , "" #. "z" #= "priv"
        ] #= "other"]
      in parses program r >>= assertEqual (banner r) e
          
  , "nested destructuring" ~: let
      r = "{ .x = .val; .y = { .z = priv } } = other"
      e = [
        [ "" #. "x" #= "" #. "val"
        , "" #. "y" #= [ "" #. "z" #= "priv" ]
        ] #= "other"]
      in parses program r >>= assertEqual (banner r) e
      
  ]

