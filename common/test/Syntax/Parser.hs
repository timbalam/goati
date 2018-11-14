{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Syntax.Parser 
  ( tests )
  where

import Goat.Syntax.Class
import Goat.Syntax.Parser (parse, Parser, NonEmpty)
import qualified Data.Text as T
import qualified Text.Parsec as P
import Test.HUnit
  
  
banner :: Show a => a -> String
banner a = "For " ++ shows a ","


parses :: Parser a -> T.Text -> IO a
parses parser input =
  either
    (ioError . userError . show)
    return
    (parse parser "parser" input)
  

fails :: Show a => Parser a -> T.Text -> Assertion
fails parser input =
  either
    (return . const ())
    (ioError . userError . show)
    (parse parser "parser" input)

tests
  :: (Eq a, Show a, Expr a, Extern a,
      Eq b, Show b, LetPatt b, Expr (Rhs b), Pun b)
  => Parser a -> Parser [b] -> Test
tests rhs program =
 test
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
    , "escape" ~: escape rhs
    , "extension" ~: extension rhs
    , "patterns" ~: patterns program
    ]
    

emptyProgram :: (Eq a, Show a) => Parser [a] -> Assertion
emptyProgram program = let
  r = ""
  e = []
  in parses program r >>= assertEqual (banner r) e

    
    
literals :: (Eq a, Show a, Lit a) => Parser a -> Test
literals rhs = test
  [ "string" ~: let
      r = "\"hi\""
      e = "hi"
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


expression :: (Eq a, Show a, Expr a) => Parser a -> Test
expression rhs = test
  [ "plain identifier" ~: let
      r = "name"
      e = local_ "name"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "period separated identifiers" ~: let
      r = "path.to.thing"
      e = local_ "path" #. "to" #. "thing"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "identifiers separated by period and space" ~: let
      r = "with. space"
      e = local_ "with" #. "space"
      in parses rhs r >>= assertEqual (banner r) e
              
  , "identifiers separated by space and period" ~: let
      r = "with .space"
      e = local_ "with" #. "space"
      in parses rhs r >>= assertEqual (banner r) e
              
  , "identifiers separated by spaces around period" ~: let
      r = "with . spaces"
      e = local_ "with" #. "spaces"
      in parses rhs r >>= assertEqual (banner r) e
          
  , "identifier with beginning period" ~: let
      r = ".local"
      e = self_ "local"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "brackets around identifier" ~: let
      r = "(bracket)"
      e = local_ "bracket" 
      in parses rhs r >>= assertEqual (banner r) e
        
  , "empty brackets not allowed" ~:
      fails rhs "()"
      
  , "parenthesised path" ~: let
      r = "(.path . path)"
      e = self_ "path" #. "path"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "parenthesised literal number" ~: let
      r = "(7)"
      e = 7
      in parses rhs r >>= assertEqual (banner r) e
      
  , "parenthesised literal string" ~: let
      r = "( \"hi, there\" )"
      e = "hi, there"
      in parses rhs r >>= assertEqual (banner r) e
      
  ]


operators :: (Eq a, Show a, Expr a) => Parser a -> Test
operators rhs = test
  [ "primitive negative number" ~: let
      r = "-45" 
      e = neg_ 45
      in parses rhs r >>= assertEqual (banner r) e
  
  , "boolean not" ~: let
      r = "!hi" 
      e = not_ (local_ "hi")
      in parses rhs r >>= assertEqual (banner r) e
  
  , "boolean and ##obsolete" ~: let
      r = "this & that"
      e = local_ "this" #& local_ "that"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "boolean or ##obsolete" ~: let
      r = "4 | 2" 
      e = 4 #| 2
      in parses rhs r >>= assertEqual (banner r) e
  
  , "addition" ~: let
      r = "10 + 3"
      e = 10 #+ 3
      in parses rhs r >>= assertEqual (banner r) e
  
  , "multiple additions" ~: let
      r = "a + b + c"
      e1 = local_ "a" #+ local_ "b" #+ local_ "c"
      e2 = (local_ "a" #+ local_ "b") #+ local_ "c"
      in do
        parses rhs r >>= assertEqual (banner r) e1
        parses rhs r >>= assertEqual (banner r) e2
  
  , "subtraction" ~: let
      r = "a - b"
      e = local_ "a" #- local_ "b"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "mixed addition and subtraction" ~: let
      r = "a + b - c"
      e1 = local_ "a" #+ local_ "b" #- local_ "c"
      e2 = (local_ "a" #+ local_ "b") #- local_ "c"
      in do
        parses rhs r >>= assertEqual (banner r) e1
        parses rhs r >>= assertEqual (banner r) e2
  
  , "multiplication" ~: let
      r = "a * 2" 
      e = local_ "a" #* 2
      in parses rhs r >>= assertEqual (banner r) e
  
  , "division" ~: let
      r = "value / 2"
      e = local_ "value" #/ 2
      in parses rhs r >>= assertEqual (banner r) e
  
  , "power ##obsolete" ~: let
      r = "3^i"
      e = 3 #^ local_ "i"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "parenthesised addition" ~: let
      r = "(a + b)"
      e = local_ "a" #+ local_ "b"
      in parses rhs r >>= assertEqual (banner r) e
  
  , "mixed operations with parentheses" ~: let
      r = "a + (b - 2)"
      e = local_ "a" #+ (local_ "b" #- 2)
      in parses rhs r >>= assertEqual (banner r) e
  
  ]
    
comparisons :: (Eq a, Show a, Expr a) => Parser a -> Test
comparisons rhs = test
  [ "greater than" ~: let
      r = "3 > 2" 
      e = 3 #> 2
      in parses rhs r >>= assertEqual (banner r) e
          
  , "less than" ~: let
      r = "2 < abc"
      e = 2 #< local_ "abc"
      in parses rhs r >>= assertEqual (banner r) e
        
  , "less or equal" ~: let
      r = "a <= b"
      e = local_ "a" #<= local_ "b"
      in parses rhs r >>= assertEqual (banner r) e
          
  , "greater or equal" ~: let
      r = "b >= 4"
      e = local_ "b" #>= 4
      in parses rhs r >>= assertEqual (banner r) e
          
  , "equal" ~: let
      r = "2 == True"
      e = 2 #== local_ "True"
      in parses rhs r >>= assertEqual (banner r) e
          
  , "not equal" ~: let
      r = "3 != 3"
      e = 3 #!= 3
      in parses rhs r >>= assertEqual (banner r) e
          
  ]
    
precedence :: (Eq a, Show a, Lit a) => Parser a -> Test
precedence rhs = test
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
  
  ]


comment :: (Eq a, Show a, Lit a) => Parser a -> Assertion
comment rhs = let 
  r = "1 // don't parse this"
  e = 1
  in parses rhs r >>= assertEqual (banner r) e


use :: (Eq a, Show a, Expr a, Extern a) => Parser a -> Test
use rhs = test
  [ "use statement" ~: let
      r = "@use name"
      e = use_ "name"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "use statement has precedence over path" ~: let
      r = "@use name.get"
      e = use_ "name" #. "get"
      in parses rhs r >>= assertEqual (banner r) e
      
  , "use statement has precedence over binary operator" ~: let
      r = "2 + @use name"
      e = 2 #+ use_ "name"
      in parses rhs r >>= assertEqual (banner r) e
      
  ]   
            
statements
  :: (Eq a, Show a, LetPatt a, Expr (Rhs a), Pun a)
  => Parser [a] -> Test
statements program = test
  [ "assignment" ~: let
        r = "assign = 1" 
        e = pure (local_ "assign" #= 1)
        in parses program r >>= assertEqual (banner r) e
            
  , "assign zero" ~: let
      r = "assign = 0"
      e = pure (local_ "assign" #= 0)
      in parses program r >>= assertEqual (banner r) e
      
  , "program begins with comment" ~: let
      r = "// comment\na = b"
      e = pure (local_ "a" #= local_ "b")
      in parses program r >>= assertEqual (banner r) e
      
  , "program contains a comment" ~: let
      r = "a = b;\n// comment line"
      e = pure (local_ "a" #= local_ "b")
      in parses program r >>= assertEqual (banner r) e
      
  ]

block
  :: (Eq a, Show a, Expr a) => Parser a -> Test
block rhs = test
  [ "rec block with assignment" ~: let
      r = "{ a = b }"
      e = block_ [ local_ "a" #= local_ "b" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "rec block with public assignment" ~: let
      r = "{ .a = b }"
      e = block_ [ self_ "a" #= local_ "b" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "rec block with punned assignment" ~: let
      r = "{ .c }"
      e = block_ [ self_ "c" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "rec block trailing semi-colon" ~: let
      r = "{ a = 1; }"
      e = block_ [ local_ "a" #= 1 ]
      in parses rhs r >>= assertEqual (banner r) e
                 
  , "rec block with multiple statements" ~: let
      r = "{ a = 1; b = a; .c }"
      e = block_
        [ local_ "a" #= 1
        , local_ "b" #= local_ "a"
        , self_ "c"
        ]
      in parses rhs r >>= assertEqual (banner r) e
        
  , "empty object" ~: let
      r = "{}"
      e = block_ []
      in parses rhs r >>= assertEqual (banner r) e
      
  , "block with self reference" ~: let
      r = "{ a = a }"
      e = block_ [ local_ "a" #= local_ "a" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  ]
  
escape :: (Eq a, Show a, Expr a) => Parser a -> Test
escape rhs = test
  [ "block with escaped definition" ~: let
      r = "{ .a = ^b }"
      e = block_ [ self_ "a" #= esc_ (local_ "b") ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "block with mixed escaped and unescaped definitions" ~: let
      r = "{ .a = 1; .b = ^a; ^c }"
      e = block_
        [ self_ "a" #= 1
        , self_ "b" #= esc_ (local_ "a")
        , esc_ (local_ "c")
        ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "single pun statement" ~: let
      r = "{ ^.a.b }"
      e = block_ [ esc_ (self_ "a" #. "b") ]
      in parses rhs r >>= assertEqual (banner r) e
      
  ]

extension
  :: (Eq a, Show a, Expr a) => Parser a -> Test
extension rhs = test
  [ "identifier with extension" ~: let
      r = "a.thing{ .f = b }"
      e = local_ "a" #. "thing" # block_ [ self_ "f" #= local_ "b" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "identifier and extension separated by space" ~: let
      r = "a.thing { .f = b }"
      e = local_ "a" #. "thing" # block_ [ self_ "f" #= local_ "b" ]
      in parses rhs r >>= assertEqual (banner r) e
           
  , "identifier beginning with period with extension" ~: let
      r = ".local {.f = update}"
      e = self_ "local" # block_ [ self_ "f" #= local_ "update" ]
      in parses rhs r >>= assertEqual (banner r) e
      
  , "extension with public pun" ~: let
      r = "a.thing { ^.f }"
      e = local_ "a" #. "thing" # block_ [ esc_ (self_ "f") ]
      in
      parses rhs r >>= assertEqual (banner r) e
           
  , "chained extensions" ~: let
      r = ".thing { .f = \"a\" }.get { .with = b }"
      e = self_ "thing" # block_ [ self_ "f" #= "a" ]
        #. "get" # block_ [ self_ "with" #= local_ "b" ]
      in parses rhs r >>= assertEqual (banner r) e
  ]
  
  
patterns 
  :: (Eq a, Show a, LetPatt a, Expr (Rhs a), Pun a)
  => Parser [a] -> Test
patterns program = test 
  [ "destructuring assignment" ~: let
      r = "{ .member = ^b } = object"
      e = pure
        (block_ [ self_ "member" #= esc_ (local_ "b") ] #= local_ "object")
      in parses program r >>= assertEqual (banner r) e
      
  , "destructuring pun" ~: let
      r = "{ ^.member } = object"
      e = pure (block_ [ esc_ (self_ "member") ] #= local_ "object")
      in
      parses program r >>= assertEqual (banner r) e
      
  , "destructuring assignment needs escaping" ~:
      fails program "{ .member = b } = object"
      
  , "destructuring pun needs escaping" ~:
      fails program "{ .member } = object"
          
  , "destructuring and unpacking statement" ~: let
      r = "rest { .x = ^.val } = thing"
      e = pure 
        (local_ "rest" # block_ [ self_ "x" #= esc_ (self_ "val") ] #= local_ "thing")
      in parses program r >>= assertEqual (banner r) e
      
  , "only unpacking statement" ~: let
      r = "rest {} = thing"
      e = pure (local_ "rest" # block_ [] #= local_ "thing")
      in parses program r >>= assertEqual (banner r) e
          
  , "destructuring with multiple statements" ~: let
      r = "{ .x = ^.val; .z = ^priv } = other"
      e = pure (block_
        [ self_ "x" #= esc_ (self_ "val")
        , self_ "z" #= esc_ (local_ "priv")
        ] #= local_ "other")
      in parses program r >>= assertEqual (banner r) e
          
  , "nested destructuring" ~: let
      r = "{ .x = ^.val; .y = ^{ .z = ^priv } } = other"
      e = pure (block_
        [ self_ "x" #= esc_ (self_ "val")
        , self_ "y" #= esc_ (block_ [ self_ "z" #= esc_ (local_ "priv") ])
        ] #= local_ "other")
      in parses program r >>= assertEqual (banner r) e
      
  ]
