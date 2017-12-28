{-# LANGUAGE OverloadedStrings #-}
module Test.Parser 
  ( tests
  ) where

import Types.Parser.Short
import Types.Parser
import Types.Classes
import Parser( program, rhs )

import Data.Function( (&) )
import qualified Data.Text as T
import Text.Parsec.Text( Parser )
import qualified Text.Parsec as P
import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","


type E = Syntax
type S = Stmt


parses :: Parser a -> T.Text -> IO a
parses parser input =
  either
    (ioError . userError . show)
    return
    (P.parse parser "test" input)
  

fails :: ShowMy a => Parser a -> T.Text -> Assertion
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
            let e = "hi" :: E
            assertEqual (banner r) e r
    
        , "integer" ~: do
            r <- parses rhs  "123"
            let e = IntegerLit 123
            assertEqual (banner r) e r
    
        , "trailing decimal" ~: do
            r <- parses rhs "123."
            let e = NumberLit 123
            assertEqual (banner r) e r
        
        , "decimal with trailing digits" ~: do
            r <- parses rhs "123.0"
            let e = NumberLit 123
            assertEqual (banner r) e r
            
        , "underscores in number" ~: do
            r <- parses rhs "1_000.2_5"
            let e = NumberLit 1000.25
            assertEqual (banner r) e r
            
        , "binary" ~: do
            r <- parses rhs "0b100"
            let e = IntegerLit 4
            assertEqual (banner r) e r
            
        , "octal" ~: do
            r <- parses rhs "0o11"
            let e = IntegerLit 9
            assertEqual (banner r) e r
            
        , "hexidecimal" ~: do
            r <- parses rhs "0xa0"
            let e = IntegerLit 160
            assertEqual (banner r) e r
            
        ]
        
    , "expression" ~:
        [ "plain identifier" ~: do
            r <- parses rhs "name"
            let e = env' "name" :: E
            assertEqual (banner r) e r
            
        , "period separated identifiers" ~: do
            r <- parses rhs "path.to.thing"
            let e = env' "path" #. "to" #. "thing"
            assertEqual (banner r) e r
        
        , "identifiers separated by period and space" ~: do
            r <- parses rhs "with. space"
            let e = env' "with" #. "space"
            assertEqual (banner r) e r
                    
        , "identifiers separated by space and period" ~: do
            r <- parses rhs "with .space"
            let e = env' "with" #. "space"
            assertEqual (banner r) e r
                    
        , "identifiers separaed by spaces around period" ~: do
            r <- parses rhs "with . spaces"
            let e = env' "with" #. "spaces"
            assertEqual (banner r) e r
                
        , "identifier with  beginning period" ~: do
            r <- parses rhs ".local"
            let e = self' "local"
            assertEqual (banner r) e r
            
        , "brackets around identifier" ~: do
            r <- parses rhs "(bracket)"
            let e = env' "bracket" 
            assertEqual (banner r) e r
              
        , "empty brackets" ~:
            fails rhs "()"
              
        , "identifier with applied brackets" ~: do
            r <- parses rhs "a.thing(applied)"
            let e = env' "a" #. "thing" # env' "applied"
            assertEqual (banner r) e r
                 
        , "identifier beginning with period with applied brackets" ~: do
            r <- parses rhs ".local(applied)"
            let e = self' "local" # env' "applied"
            assertEqual (banner r) e r
                 
        , "chained applications" ~: do
            r <- parses rhs ".thing(a).get(b)"
            let e = self' "thing" # (env' "a") #. "get" # (env' "b")
            assertEqual (banner r) e r
                  
        ]
        
    , "operators" ~:
        [ "primitive negative number" ~: do
            r <- parses rhs "-45" 
            let e = -45 :: E
            assertEqual (banner r) e r
              
        , "boolean not" ~: do
            r <- parses rhs "!hi" 
            let e = not' (env' "hi") :: E
            assertEqual (banner r) e r
              
        , "boolean and" ~: do
            r <- parses rhs "this & that"
            let e = env' "this" #& env' "that"
            assertEqual (banner r) e r
                 
        , "boolean or" ~: do
            r <- parses rhs "4 | 2" 
            let e = 4 #| 2 :: E
            assertEqual (banner r) e r
                 
        , "addition" ~: do
            r <- parses rhs "10 + 3"
            let e = 10 #+ 3 :: E
            assertEqual (banner r) e r
                 
        , "multiple additions" ~: do
            r <- parses rhs "a + b + c"
            let
              e1 = env' "a" #+ env' "b" #+ env' "c"
              e2 =
                (Var (Intern (Priv "a")) & Binop Add $ Var (Intern (Priv "b")))
                  & Binop Add $ Var (Intern (Priv "c"))
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
        , "subtraction" ~: do
            r <- parses rhs "a - b"
            let e = env' "a" #- env' "b"
            assertEqual (banner r) e r
                 
        , "mixed addition and subtraction" ~: do
            r <- parses rhs "a + b - c"
            let 
              e1 = env' "a" #+ env' "b" #- env' "c"
              e2 =
                (Var (Intern (Priv "a")) & Binop Add $ Var (Intern (Priv "b")))
                  & Binop Sub $ Var (Intern (Priv "c"))
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
                
        , "multiplication" ~: do
            r <- parses rhs "a * 2" 
            let e = env' "a" #* 2
            assertEqual (banner r) e r
                 
        , "division" ~: do
            r <- parses rhs "value / 2"
            let e = env' "value" #/ 2
            assertEqual (banner r) e r
                 
        , "power" ~: do
            r <- parses rhs "3^i"
            let e = 3 #^ env' "i"
            assertEqual (banner r) e r
             
        ]
        
    , "comparisons" ~:
        [ "greater than" ~: do
            r <- parses rhs "3 > 2" 
            let e = 3 #> 2
            assertEqual (banner r) e r
                
        , "less than" ~: do
            r <- parses rhs "2 < abc"
            let e = 2 #< env' "abc"
            assertEqual (banner r) e r
              
        , "less or equal" ~: do
            r <- parses rhs "a <= b"
            let e = env' "a" #<= env' "b"
            assertEqual (banner r) e r
                
        , "greater or equal" ~: do
            r <- parses rhs "b >= 4"
            let e = env' "b" #>= 4
            assertEqual (banner r) e r
                
        , "equal" ~: do
            r <- parses rhs "2 == True"
            let e = 2 #== env' "True"
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
              e2 =
                ((IntegerLit 1 & Binop Add $ IntegerLit 1)
                  & Binop Add $ IntegerLit 3)
                  & Binop And $
                    (IntegerLit 5 & Binop Sub $ IntegerLit 1)
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                    
        , "addition, subtration and multiplication" ~: do
            r <- parses rhs "1 + 1 + 3 * 5 - 1"
            let
              e1 = 1 #+ 1 #+ 3 #* 5 #- 1
              e2 =
                ((IntegerLit 1 & Binop Add $ IntegerLit 1)
                  & Binop Add $
                    (IntegerLit 3 & Binop Prod $ IntegerLit 5))
                  & Binop Sub $ IntegerLit 1
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
        ]
        
    , "comment" ~: do 
        r <- parses rhs "1 // don't parse this"
        let e = IntegerLit 1
        assertEqual (banner r) e r
            
    , "assignment" ~: do
        r <- parses program "assign = 1" 
        let e = pure (env' "assign" #= 1 :: S)
        assertEqual (banner r) e r
            
    , "assign zero" ~: do
        r <- parses program "assign = 0"
        let e = pure (env' "assign" #= 0 :: S)
        assertEqual (banner r) e r
    
    , "declare" ~: do
        r <- parses program "undef ="
        let e = pure (Declare (env' "undef") :: S)
        assertEqual (banner r) e r
             
    , "object with assignment" ~: do
        r <- parses rhs "{ a = b }"
        let e = block' [ env' "a" #= env' "b" ]
        assertEqual (banner r) e r
                   
    , "object with multiple statements" ~: do
        r <- parses rhs "{ a = 1; b = a; c }"
        let
          e = block' [
            env' "a" #= 1,
            env' "b" #= env' "a",
            env' "c"
            ]
        assertEqual (banner r) e r  
          
    , "empty object" ~: do
        r <- parses rhs "{}"
        let e = block' []
        assertEqual (banner r) e r
        
    , "object extension" ~: do
        r <- parses rhs "{ a = 1 ... c }"
        let e = block'' [ env' "a" #= 1 ] (env' "c")
        assertEqual (banner r) e r
        
    , "extension to self field" ~: do
        r <- parses rhs "{ a = 1 ... .field }"
        let e = block'' [ env' "a" #= 1 ] (self' "field")
        assertEqual (banner r) e r
        
    , "just extension statement" ~: do
        r <- parses rhs "{ ... x }"
        let e = block'' [] (env' "x")
        assertEqual (banner r) e r
        
    , "illegal extensions" ~:
      [ "multiple extensions" ~: do
          fails rhs "{ a = 1 ... b ... c }"
          
      , "set break before extension" ~: do
          fails rhs "{ a = 1; ... b }"
          
      , "four dots" ~: do
          fails rhs "{ a = 1; ....field }"
          
      , "statements after extension" ~: do
          fails rhs "{ ... hi; b = 2 }"
          
      ]
        
    , "destructuring assignment" ~: do
        r <- parses program "{ .member = b } = object"
        let e = pure (setblock' [ self' "member" #= env' "b" ] #= env' "object" :: S)
        assertEqual (banner r) e r
            
    , "destructuring and unpacking statement" ~: do
        r <- parses program "{ .x = .val ... rest } = thing"
        let e = pure (setblock'' [ self' "x" #= self' "val" ] (env' "rest") #= env' "thing" :: S)
        assertEqual (banner r) e r
        
    , "only unpacking statement" ~: do
        r <- parses program "{ ... rest } = thing"
        let e = pure (setblock'' [] (env' "rest") #= env' "thing" :: S)
        assertEqual (banner r) e r
        
    , "statement following unpacking statement" ~: do
        fails program "{ ... rest; x = var } = hi"
            
    , "destructuring with multiple statements" ~: do
        r <- parses program "{ .x = .val; .z = priv } = other"
        let
          e = pure (setblock' [
            self' "x" #= self' "val", 
            self' "z" #= env' "priv"
            ] #= env' "other" :: S)
        assertEqual (banner r) e r
            
    , "nested destructuring" ~: do
        r <- parses program "{ .x = .val; .y = { .z = priv } } = other"
        let
          e = pure (setblock' [
            self' "x" #= self' "val",
            self' "y" #= setblock' [ self' "z" #= env' "priv" ]
            ] #= env' "other" :: S)
        assertEqual (banner r) e r
        
    ]