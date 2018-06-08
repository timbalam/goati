{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Parser 
  ( tests
  ) where

import My.Types.Syntax.Class
import My.Parser (parse, Parser)
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
  :: (Eq a, Show a, Feat a, Extern a, Syntax (Member a), Eq b, Show b, Global b, Body b ~ b)
  => Parser a -> Parser b -> Test
tests rhs program =
 test
    [ "empty program"  ~: 
        fails program ""
    
    , "literals" ~:
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
        
    , "expression" ~:
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
                    
        , "identifiers separaed by spaces around period" ~: let
            r = "with . spaces"
            e = local_ "with" #. "spaces"
            in parses rhs r >>= assertEqual (banner r) e
                
        , "identifier with  beginning period" ~: let
            r = ".local"
            e = self_ "local"
            in parses rhs r >>= assertEqual (banner r) e
            
        , "brackets around identifier" ~: let
            r = "(bracket)"
            e = local_ "bracket" 
            in parses rhs r >>= assertEqual (banner r) e
              
        , "empty brackets" ~: let
            r = "()"
            e = tup_ empty_
            in parses rhs r >>= assertEqual (banner r) e
            
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
        
    , "operators" ~:
        [ "primitive negative number" ~: let
            r = "-45" 
            e = neg_ 45
            in parses rhs r >>= assertEqual (banner r) e
              
        , "boolean not" ~: let
            r = "!hi" 
            e = not_ (local_ "hi")
            in parses rhs r >>= assertEqual (banner r) e
              
        , "boolean and" ~: let
            r = "this & that"
            e = local_ "this" #& local_ "that"
            in parses rhs r >>= assertEqual (banner r) e
                 
        , "boolean or" ~: let
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
                 
        , "power" ~: let
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
        
    , "comparisons" ~:
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
        
    , "mixed numeric and boolean operations" ~:
        [ "addition and subtraction" ~: let
            r = "1 + 1 + 3 & 5 - 1"
            e1 = 1 #+ 1 #+ 3 #& 5 #- 1
            e2 = ((1 #+ 1) #+ 3) #& (5 #- 1)
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
        
    , "comment" ~: let 
        r = "1 // don't parse this"
        e = 1
        in parses rhs r >>= assertEqual (banner r) e
        
    , "use statement" ~: let
        r = "@use name"
        e = use_ "name"
        in parses rhs r >>= assertEqual (banner r) e
        
    , "parenthesised use statement in path" ~: let
        r = "(@use name).get"
        e = use_ "name" #. "get"
        in parses rhs r >>= assertEqual (banner r) e
        
    , "use statement in numeric expression" ~: let
        r = "2 + @use name"
        e = 2 #+ use_ "name"
        in parses rhs r >>= assertEqual (banner r) e
        
    , "must parenthesis use statement in expression" ~:
        fails rhs "@use name.field"
            
    , "assignment" ~: let
        r = "assign = 1" 
        e = local_ "assign" #= 1
        in parses program r >>= assertEqual (banner r) e
            
    , "assign zero" ~: let
        r = "assign = 0"
        e = local_ "assign" #= 0
        in parses program r >>= assertEqual (banner r) e
             
    , "rec block with assignment" ~: let
        r = "{ a = b }"
        e = block_ ( local_ "a" #= local_ "b" )
        in parses rhs r >>= assertEqual (banner r) e
        
    , "tup block with assignment" ~: let
        r = "( .a = b,)"
        e = tup_ ( self_ "a" #= local_ "b" )
        in parses rhs r >>= assertEqual (banner r) e
                   
    , "rec block with multiple statements" ~: let
        r = "{ a = 1; b = a; .c }"
        e = block_ (
          local_ "a" #= 1 #:
          local_ "b" #= local_ "a" #:
          self_ "c"
          )
        in parses rhs r >>= assertEqual (banner r) e  
        
    , "rec block trailing semi-colon" ~: let
        r = "{ a = 1; }"
        e = block_ ( local_ "a" #= 1 )
        in parses rhs r >>= assertEqual (banner r) e
          
    , "empty object" ~: let
        r = "{}"
        e = block_ empty_
        in parses rhs r >>= assertEqual (banner r) e
        
    , "tup block with multiple statements" ~: let
        r = "( .a = 1, .b = a, c )"
        e = tup_ (
          self_ "a" #= 1 #:
          self_ "b" #= local_ "a" #:
          local_ "c"
          )
        in parses rhs r >>= assertEqual (banner r) e
        
    , "tup block with path assignment" ~: let
        r = "( .a.b = 2,)"
        e = tup_ ( self_ "a" #. "b" #= 2 )
        in parses rhs r >>= assertEqual (banner r) e
        
    , "trailing comma required for single" ~:
        fails rhs "( .a.b = 2 )"
    
    , "tup block with trailing comma" ~: let
        r = "( .a = 1, .g = .f,)"
        e = tup_ (
          self_ "a" #= 1 #:
          self_ "g" #= self_ "f"
          )
        in parses rhs r >>= assertEqual (banner r) e
              
    , "extension" ~:
        [ "identifier with extension" ~: let
            r = "a.thing{ .f = b }"
            e = local_ "a" #. "thing" # block_ ( self_ "f" #= local_ "b" )
            in parses rhs r >>= assertEqual (banner r) e
            
        , "identifier and extension separated by space" ~: let
            r = "a.thing { .f = b }"
            e = local_ "a" #. "thing" # block_ ( self_ "f" #= local_ "b" )
            in parses rhs r >>= assertEqual (banner r) e
                 
        , "identifier beginning with period with extension" ~: let
            r = ".local { .f = update }"
            e = self_ "local" # block_ ( self_ "f" #= local_ "update" )
            in parses rhs r >>= assertEqual (banner r) e
            
        , "extension with tup block" ~: let
            r = "a.thing ( .f = b,)"
            e = local_ "a" #. "thing" # tup_ ( self_ "f" #= local_ "b" )
            in parses rhs r >>= assertEqual (banner r) e
            
        , "extension with tup block needs trailing comma" ~:
            fails rhs "a.thing ( .f = b )"
                 
        , "chained extensions" ~: let
            r = ".thing { .f = \"a\" }.get { .with = b }"
            e = self_ "thing" # block_ ( self_ "f" #= "a" )
              #. "get" # block_ ( self_ "with" #= local_ "b" )
            in parses rhs r >>= assertEqual (banner r) e
        ]
        
    , "program begins with comment" ~: let
        r = "// comment\na = b"
        e = local_ "a" #= local_ "b"
        in parses program r >>= assertEqual (banner r) e
        
    , "program contains a comment" ~: let
        r = "a = b;\n// comment line"
        e = local_ "a" #= local_ "b"
        in parses program r >>= assertEqual (banner r) e
        
    , "destructuring assignment" ~: let
        r = "( .member = b,) = object"
        e = tup_ ( self_ "member" #= local_ "b" ) #= local_ "object"
        in parses program r >>= assertEqual (banner r) e
        
    , "destructuring tup needs trailing comma" ~:
        fails program "( .member = b ) = object"
            
    , "destructuring and unpacking statement" ~: let
        r = "rest ( .x = .val,) = thing"
        e = local_ "rest" # tup_ ( self_ "x" #= self_ "val" ) #= local_ "thing"
        in parses program r >>= assertEqual (banner r) e
        
    , "destructuring with tup block only" ~:
        fails program "{ .member = b } = object"
        
    , "only unpacking statement" ~: let
        r = "rest () = thing"
        e = local_ "rest" # tup_ empty_ #= local_ "thing"
        in parses program r >>= assertEqual (banner r) e
            
    , "destructuring with multiple statements" ~: let
        r = "( .x = .val, .z = priv ) = other"
        e = tup_ (
          self_ "x" #= self_ "val" #: 
          self_ "z" #= local_ "priv"
          ) #= local_ "other"
        in parses program r >>= assertEqual (banner r) e
            
    , "nested destructuring" ~: let
        r = "( .x = .val, .y = ( .z = priv,) ) = other"
        e = tup_ (
          self_ "x" #= self_ "val" #:
          self_ "y" #= tup_ ( self_ "z" #= local_ "priv" )
          ) #= local_ "other"
        in parses program r >>= assertEqual (banner r) e
        
    ]