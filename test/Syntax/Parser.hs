{-# LANGUAGE OverloadedStrings, TypeFamilies #-}

module Syntax.Parser 
  ( tests
  ) where

--import My.Types.Parser.Short
import My.Types.Syntax.Class
import My.Types.Parser (Name, Ident, Key, Import)
import qualified My.Types.Parser as P
import My.Parser (ShowMy(..))
import qualified My.Syntax.Parser as P 
import Data.Function( (&) )
import Data.Semigroup ( (<>) )
import qualified Data.Text as T
import qualified Text.Parsec as P
import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","


rhs :: P.Parser (P.Expr (Name Ident Key Import))
rhs = P.syntax <* P.eof

program :: P.Parser (P.Program Import)
program = P.program


parses :: P.Parser a -> T.Text -> IO a
parses parser input =
  either
    (ioError . userError . show)
    return
    (P.parse parser "test" input)
  

fails :: (ShowMy a) => P.Parser a -> T.Text -> Assertion
fails parser input =
  either
    (return . const ())
    (ioError . userError . showMy)
    (P.parse parser "test" input)


tests =
 test
    [ "empty program"  ~: 
        fails program ""
    
    , "literals" ~:
        [ "string" ~: do
            r <- parses rhs "\"hi\""
            let e = "hi"
            assertEqual (banner r) e r
    
        , "integer" ~: do
            r <- parses rhs "123"
            let e = 123
            assertEqual (banner r) e r
    
        , "trailing decimal" ~: do
            r <- parses rhs "123."
            let e = 123.0
            assertEqual (banner r) e r
        
        , "decimal with trailing digits" ~: do
            r <- parses rhs "123.0"
            let e = 123.0
            assertEqual (banner r) e r
            
        , "underscores in number" ~: do
            r <- parses rhs "1_000.2_5"
            let e = 1000.25
            assertEqual (banner r) e r
            
        , "binary" ~: do
            r <- parses rhs "0b100"
            let e = 4
            assertEqual (banner r) e r
            
        , "octal" ~: do
            r <- parses rhs "0o11"
            let e = 9
            assertEqual (banner r) e r
            
        , "hexidecimal" ~: do
            r <- parses rhs "0xa0"
            let e = 160
            assertEqual (banner r) e r
            
        ]
        
    , "expression" ~:
        [ "plain identifier" ~: do
            r <- parses rhs "name"
            let e = local_ "name"
            assertEqual (banner r) e r
            
        , "period separated identifiers" ~: do
            r <- parses rhs "path.to.thing"
            let e = local_ "path" #. "to" #. "thing"
            assertEqual (banner r) e r
        
        , "identifiers separated by period and space" ~: do
            r <- parses rhs "with. space"
            let e = local_ "with" #. "space"
            assertEqual (banner r) e r
                    
        , "identifiers separated by space and period" ~: do
            r <- parses rhs "with .space"
            let e = local_ "with" #. "space"
            assertEqual (banner r) e r
                    
        , "identifiers separaed by spaces around period" ~: do
            r <- parses rhs "with . spaces"
            let e = local_ "with" #. "spaces"
            assertEqual (banner r) e r
                
        , "identifier with beginning period" ~: do
            r <- parses rhs ".local"
            let e = self_ "local"
            assertEqual (banner r) e r
            
        , "brackets around identifier" ~: do
            r <- parses rhs "(bracket)"
            let e = local_ "bracket" 
            assertEqual (banner r) e r
              
        , "empty brackets" ~: do
            r <- parses rhs "()"
            let e = tup_ empty_
            assertEqual (banner r) e r
            
        , "parenthesised path" ~: do
            r <- parses rhs "(.path . path)"
            let e = self_ "path" #. "path"
            assertEqual (banner r) e r
            
        , "parenthesised literal number" ~: do
            r <- parses rhs "(7)"
            let e = 7
            assertEqual (banner r) e r
            
        , "parenthesised literal string" ~: do
            r <- parses rhs "( \"hi, there\" )"
            let e = "hi, there"
            assertEqual (banner r) e r
            
        ]
        
    , "operators" ~:
        [ "primitive negative number" ~: do
            r <- parses rhs "-45" 
            let e = neg_ 45
            assertEqual (banner r) e r
              
        , "boolean not" ~: do
            r <- parses rhs "!hi" 
            let e = not_ (local_ "hi")
            assertEqual (banner r) e r
              
        , "boolean and" ~: do
            r <- parses rhs "this & that"
            let e = local_ "this" #& local_ "that"
            assertEqual (banner r) e r
                 
        , "boolean or" ~: do
            r <- parses rhs "4 | 2" 
            let e = 4 #| 2
            assertEqual (banner r) e r
                 
        , "addition" ~: do
            r <- parses rhs "10 + 3"
            let e = 10 #+ 3
            assertEqual (banner r) e r
                 
        , "multiple additions" ~: do
            r <- parses rhs "a + b + c"
            let
              e1 = local_ "a" #+ local_ "b" #+ local_ "c"
              e2 = (local_ "a" #+ local_ "b") #+ local_ "c"
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
        , "subtraction" ~: do
            r <- parses rhs "a - b"
            let e = local_ "a" #- local_ "b"
            assertEqual (banner r) e r
                 
        , "mixed addition and subtraction" ~: do
            r <- parses rhs "a + b - c"
            let 
              e1 = local_ "a" #+ local_ "b" #- local_ "c"
              e2 = (local_ "a" #+ local_ "b") #- local_ "c"
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
                
        , "multiplication" ~: do
            r <- parses rhs "a * 2" 
            let e = local_ "a" #* 2
            assertEqual (banner r) e r
                 
        , "division" ~: do
            r <- parses rhs "value / 2"
            let e = local_ "value" #/ 2
            assertEqual (banner r) e r
                 
        , "power" ~: do
            r <- parses rhs "3^i"
            let e = 3 #^ local_ "i"
            assertEqual (banner r) e r
            
        , "parenthesised addition" ~: do
            r <- parses rhs "(a + b)"
            let e = local_ "a" #+ local_ "b"
            assertEqual (banner r) e r
            
        , "mixed operations with parentheses" ~: do
            r <- parses rhs "a + (b - 2)"
            let e = local_ "a" #+ (local_ "b" #- 2)
            assertEqual (banner r) e r
             
        ]
        
    , "comparisons" ~:
        [ "greater than" ~: do
            r <- parses rhs "3 > 2" 
            let e = 3 #> 2
            assertEqual (banner r) e r
                
        , "less than" ~: do
            r <- parses rhs "2 < abc"
            let e = 2 #< local_ "abc"
            assertEqual (banner r) e r
              
        , "less or equal" ~: do
            r <- parses rhs "a <= b"
            let e = local_ "a" #<= local_ "b"
            assertEqual (banner r) e r
                
        , "greater or equal" ~: do
            r <- parses rhs "b >= 4"
            let e = local_ "b" #>= 4
            assertEqual (banner r) e r
                
        , "equal" ~: do
            r <- parses rhs "2 == True"
            let e = 2 #== local_ "True"
            assertEqual (banner r) e r
                
        , "not equal" ~: do
            r <- parses rhs "3 != 3"
            let e = 3 #!= 3
            assertEqual (banner r) e r
                
        ]
        
    , "mixed numeric and boolean operations" ~:
        [ "addition and subtraction" ~: do
            r <- parses rhs "1 + 1 + 3 & 5 - 1"
            let
              e1 = 1 #+ 1 #+ 3 #& 5 #- 1
              e2 = ((1 #+ 1) #+ 3) #& (5 #- 1)
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                    
        , "addition, subtration and multiplication" ~: do
            r <- parses rhs "1 + 1 + 3 * 5 - 1"
            let
              e1 = 1 #+ 1 #+ 3 #* 5 #- 1
              e2 = ((1 #+ 1) #+ (3 #* 5)) #- 1
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
        ]
        
    , "comment" ~: do 
        r <- parses rhs "1 // don't parse this"
        let e = 1
        assertEqual (banner r) e r
        
    , "use statement" ~: do
        r <- parses rhs "@use name"
        let e = use_ "name"
        assertEqual (banner r) e r
        
    , "parenthesised use statement in path" ~: do
        r <- parses rhs "(@use name).get"
        let e = use_ "name" #. "get"
        assertEqual (banner r) e r
        
    , "use statement in numeric expression" ~: do
        r <- parses rhs "2 + @use name"
        let e = 2 #+ use_ "name"
        assertEqual (banner r) e r
        
    , "must parenthesise use statement in expression" ~: do
        fails rhs "@use name.field"
        
    , "assignment" ~: do
        r <- parses program "assign = 1" 
        let e = local_ "assign" #= 1
        assertEqual (banner r) e r
    
    , "assign zero" ~: do
        r <- parses program "assign = 0"
        let e = local_ "assign" #= 0
        assertEqual (banner r) e r  
             
    , "rec block with assignment" ~: do
        r <- parses rhs "{ a = b }"
        let e = block_ ( local_ "a" #= local_ "b" )
        assertEqual (banner r) e r
            
    , "tup block with assignment" ~: do
        r <- parses rhs "( .a = b,)"
        let e = tup_ ( self_ "a" #= local_ "b" )
        assertEqual (banner r) e r
                   
    , "rec block with multiple statements" ~: do
        r <- parses rhs "{ a = 1; b = a; .c }"
        let
          e = block_
            ( local_ "a" #= 1
            #: local_ "b" #= local_ "a"
            #: self_ "c"
            )
        assertEqual (banner r) e r  
        
    , "rec block trailing semi-colon" ~: do
        r <- parses rhs "{ a = 1; }"
        let e = block_ ( local_ "a" #= 1 )
        assertEqual (banner r) e r
          
    , "empty object" ~: do
        r <- parses rhs "{}"
        let e = block_ empty_
        assertEqual (banner r) e r
        
    , "tup block with multiple statements" ~: do
        r <- parses rhs "( .a = 1, .b = a, c )"
        let
          e = tup_
            ( self_ "a" #= 1
            #: self_ "b" #= local_ "a"
            #: local_ "c"
            )
        assertEqual (banner r) e r
        
    , "tup block with path assignment" ~: do
        r <- parses rhs "( .a.b = 2,)"
        let e = tup_ ( self_ "a" #. "b" #= 2 )
        assertEqual (banner r) e r
        
    , "trailing comma required for single" ~: do
        fails rhs "( .a.b = 2 )"
    
    , "tup block with trailing comma" ~: do
        r <- parses rhs "( .a = 1, .g = .f,)"
        let
          e = tup_
            ( self_ "a" #= 1
            #: self_ "g" #= self_ "f"
            )
        assertEqual (banner r) e r
              
    , "extension" ~:
        [ "identifier with extension" ~: do
            r <- parses rhs "a.thing{ .f = b }"
            let e = local_ "a" #. "thing" # block_ ( self_ "f" #= local_ "b" )
            assertEqual (banner r) e r
            
        , "identifier and extension separated by space" ~: do
            r <- parses rhs "a.thing { .f = b }"
            let e = local_ "a" #. "thing" # block_ ( self_ "f" #= local_ "b" )
            assertEqual (banner r) e r
                 
        , "identifier beginning with period with extension" ~: do
            r <- parses rhs ".local { .f = update }"
            let e = self_ "local" # block_ ( self_ "f" #= local_ "update" )
            assertEqual (banner r) e r
            
        , "extension with tup block" ~: do
            r <- parses rhs "a.thing ( .f = b,)"
            let e = local_ "a" #. "thing" # tup_ ( self_ "f" #= local_ "b" )
            assertEqual (banner r) e r
            
        , "extension with tup block needs trailing comma" ~: do
            fails rhs "a.thing ( .f = b )"
                 
        , "chained extensions" ~: do
            r <- parses rhs ".thing { .f = \"a\" }.get { .with = b }"
            let
              e = self_ "thing" # block_ ( self_ "f" #= "a" )
                #. "get" # block_ ( self_ "with" #= local_ "b" )
            assertEqual (banner r) e r
        ]          
        
    , "destructuring assignment" ~: do
        r <- parses program "( .member = b,) = object"
        let e = tup_ (self_ "member" #= local_ "b") #= local_ "object"
        assertEqual (banner r) e r
        
    , "destructuring tup needs trailing comma" ~: do
        fails program "( .member = b ) = object"
            
    , "destructuring and unpacking statement" ~: do
        r <- parses program "rest ( .x = .val,) = thing"
        let e = local_ "rest" # tup_ (self_ "x" #= self_ "val") #= local_ "thing"
        assertEqual (banner r) e r
        
    , "destructuring with tup block only" ~: do
        fails program "{ .member = b } = object"
        
    , "only unpacking statement" ~: do
        r <- parses program "rest () = thing"
        let e = local_ "rest" # tup_ empty_ #= local_ "thing"
        assertEqual (banner r) e r
            
    , "destructuring with multiple statements" ~: do
        r <- parses program "( .x = .val, .z = priv ) = other"
        let
          e = tup_
            (self_ "x" #= self_ "val"
            #: self_ "z" #= local_ "priv"
            ) #= local_ "other"
        assertEqual (banner r) e r
            
    , "nested destructuring" ~: do
        r <- parses program "( .x = .val, .y = ( .z = priv,) ) = other"
        let
          --e :: (Global p, Body p ~ p) => p
          e = tup_
            (self_ "x" #= self_ "val"
            #: self_ "y" #= tup_ (self_ "z" #= local_ "priv")
            ) #= local_ "other"
        assertEqual (banner r) e r
    ]