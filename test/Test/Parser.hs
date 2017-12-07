{-# LANGUAGE OverloadedStrings #-}
module Test.Parser 
  ( tests
  ) where

import Types.Parser.Short
import Types.Classes
--import qualified Types.Error as E
import Parser( program, rhs )

import Data.Function( (&) )
import qualified Data.Text as T
import Text.Parsec.Text( Parser )
import qualified Text.Parsec as P
import Test.HUnit
  ( Test(..)
  , Assertion(..)
  , assertEqual
  , assertFailure
  , assertBool
  )
  
  
banner :: ShowMy a => a -> String
banner a = "For " ++ showMy a ++ ","


type E = Expr (Vis Tag)
type S = Stmt (Vis Tag)


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
 TestList
    [ TestLabel "empty program" . TestCase $
        fails program ""
    
    , TestLabel "literals" . TestList $
        [ TestLabel "string" . TestCase $ do
            r <- parses rhs "\"hi\""
            let e = "hi" :: E
            assertEqual (banner r) e r
    
        , TestLabel "integer" . TestCase $ do
            r <- parses rhs  "123"
            let e = IntegerLit 123
            assertEqual (banner r) e r
    
        , TestLabel "trailing decimal" . TestCase $ do
            r <- parses rhs "123."
            let e = NumberLit 123
            assertEqual (banner r) e r
        
        , TestLabel "decimal with trailing digits" . TestCase $ do
            r <- parses rhs "123.0"
            let e = NumberLit 123
            assertEqual (banner r) e r
            
        , TestLabel "underscores in number" . TestCase $ do
            r <- parses rhs "1_000.2_5"
            let e = NumberLit 1000.25
            assertEqual (banner r) e r
            
        , TestLabel "binary" . TestCase $ do
            r <- parses rhs "0b100"
            let e = IntegerLit 4
            assertEqual (banner r) e r
            
        , TestLabel "octal" . TestCase $ do
            r <- parses rhs "0o11"
            let e = IntegerLit 9
            assertEqual (banner r) e r
            
        , TestLabel "hexidecimal" . TestCase $ do
            r <- parses rhs "0xa0"
            let e = IntegerLit 160
            assertEqual (banner r) e r
            
        ]
        
    , TestLabel "expression" . TestList $
        [ TestLabel "plain identifier" . TestCase $ do
            r <- parses rhs "name"
            let e = env' "name" :: E
            assertEqual (banner r) e r
            
        , TestLabel "period separated identifiers" . TestCase $ do
            r <- parses rhs "path.to.thing"
            let e = env' "path" #. "to" #. "thing"
            assertEqual (banner r) e r
        
        , TestLabel "identifiers separated by period and space" . TestCase $ do
            r <- parses rhs "with. space"
            let e = env' "with" #. "space"
            assertEqual (banner r) e r
                    
        , TestLabel "identifiers separated by space and period" . TestCase $ do
            r <- parses rhs "with .space"
            let e = env' "with" #. "space"
            assertEqual (banner r) e r
                    
        , TestLabel "identifiers separaed by spaces around period" . TestCase $ do
            r <- parses rhs "with . spaces"
            let e = env' "with" #. "spaces"
            assertEqual (banner r) e r
                
        , TestLabel "identifier with  beginning period" . TestCase $ do
            r <- parses rhs ".local"
            let e = self' "local"
            assertEqual (banner r) e r
            
        , TestLabel "brackets around identifier" . TestCase $ do
            r <- parses rhs "(bracket)"
            let e = env' "bracket" 
            assertEqual (banner r) e r
              
        , TestLabel "empty brackets" . TestCase $
            fails rhs "()"
              
        , TestLabel "identifier with applied brackets" . TestCase $ do
            r <- parses rhs "a.thing(applied)"
            let e = env' "a" #. "thing" # env' "applied"
            assertEqual (banner r) e r
                 
        , TestLabel "identifier beginning with period with applied brackets" . TestCase $ do
            r <- parses rhs ".local(applied)"
            let e = self' "local" # env' "applied"
            assertEqual (banner r) e r
                 
        , TestLabel "chained applications" . TestCase $ do
            r <- parses rhs ".thing(a).get(b)"
            let e = self' "thing" # (env' "a") #. "get" # (env' "b")
            assertEqual (banner r) e r
                  
        ]
        
    , TestLabel "operators" . TestList $
        [ TestLabel "primitive negative number" . TestCase $ do
            r <- parses rhs "-45" 
            let e = -45 :: E
            assertEqual (banner r) e r
              
        , TestLabel "boolean not" . TestCase $ do
            r <- parses rhs "!hi" 
            let e = not' (env' "hi") :: E
            assertEqual (banner r) e r
              
        , TestLabel "boolean and" . TestCase $ do
            r <- parses rhs "this & that"
            let e = env' "this" #& env' "that"
            assertEqual (banner r) e r
                 
        , TestLabel "boolean or" . TestCase $ do
            r <- parses rhs "4 | 2" 
            let e = 4 #| 2 :: E
            assertEqual (banner r) e r
                 
        , TestLabel "addition" . TestCase $ do
            r <- parses rhs "10 + 3"
            let e = 10 #+ 3 :: E
            assertEqual (banner r) e r
                 
        , TestLabel "multiple additions" . TestCase $ do
            r <- parses rhs "a + b + c"
            let
              e1 = env' "a" #+ env' "b" #+ env' "c"
              e2 =
                (Var (Priv "a") & Binop Add $ Var (Priv "b"))
                  & Binop Add $ Var (Priv "c")
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
        , TestLabel "subtraction" . TestCase $ do
            r <- parses rhs "a - b"
            let e = env' "a" #- env' "b"
            assertEqual (banner r) e r
                 
        , TestLabel "mixed addition and subtraction" . TestCase $ do
            r <- parses rhs "a + b - c"
            let 
              e1 = env' "a" #+ env' "b" #- env' "c"
              e2 =
                (Var (Priv "a") & Binop Add $ Var (Priv "b"))
                  & Binop Sub $ Var (Priv "c")
            assertEqual (banner r) e1 r
            assertEqual (banner r) e2 r
                  
                
        , TestLabel "multiplication" . TestCase $ do
            r <- parses rhs "a * 2" 
            let e = env' "a" #* 2
            assertEqual (banner r) e r
                 
        , TestLabel "division" . TestCase $ do
            r <- parses rhs "value / 2"
            let e = env' "value" #/ 2
            assertEqual (banner r) e r
                 
        , TestLabel "power" . TestCase $ do
            r <- parses rhs "3^i"
            let e = 3 #^ env' "i"
            assertEqual (banner r) e r
             
        ]
        
    , TestLabel "comparisons" . TestList $
        [ TestLabel "greater than" . TestCase $ do
            r <- parses rhs "3 > 2" 
            let e = 3 #> 2
            assertEqual (banner r) e r
                
        , TestLabel "less than" . TestCase $ do
            r <- parses rhs "2 < abc"
            let e = 2 #< env' "abc"
            assertEqual (banner r) e r
              
        , TestLabel "less or equal" . TestCase $ do
            r <- parses rhs "a <= b"
            let e = env' "a" #<= env' "b"
            assertEqual (banner r) e r
                
        , TestLabel "greater or equal" . TestCase $ do
            r <- parses rhs "b >= 4"
            let e = env' "b" #>= 4
            assertEqual (banner r) e r
                
        , TestLabel "equal" . TestCase $ do
            r <- parses rhs "2 == True"
            let e = 2 #== env' "True"
            assertEqual (banner r) e r
                
        , TestLabel "not equal" . TestCase $ do
            r <- parses rhs "3 != 3"
            let e = 3 #!= 3
            assertEqual (banner r) e r
                
        ]
        
    , TestLabel "mixed numeric and boolean operations" . TestList $
        [ TestLabel "addition and subtraction" . TestCase $ do
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
                    
        , TestLabel "addition, subtration and multiplication" . TestCase $ do
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
            
    , TestLabel "assignment" . TestCase $ do
        r <- parses program "assign = 1" 
        let e = pure (env' "assign" #= 1 :: S)
        assertEqual (banner r) e r
            
    , TestLabel "assign zero" . TestCase $ do
        r <- parses program "assign = 0"
        let e = pure (env' "assign" #= 0 :: S)
        assertEqual (banner r) e r
    
    , TestLabel "declare" . TestCase $ do
        r <- parses program "undef ="
        let e = pure (Declare (env' "undef") :: S)
        assertEqual (banner r) e r
             
    , TestLabel "object with assignment" . TestCase $ do
        r <- parses rhs "{ a = b }"
        let e = block' [ env' "a" #= env' "b" ]
        assertEqual (banner r) e r
                   
    , TestLabel "object with multiple statements" . TestCase $ do
        r <- parses rhs "{ a = 1; b = a; c }"
        let
          e = block' [
            env' "a" #= 1,
            env' "b" #= env' "a",
            env' "c"
            ]
        assertEqual (banner r) e r  
          
    , TestLabel "empty object" . TestCase $ do
        r <- parses rhs "{}"
        let e = block' []
        assertEqual (banner r) e r
        
    , TestLabel "destructuring assignment" . TestCase $ do
        r <- parses program "{ .member = b } = object"
        let e = pure (setblock' [ self' "member" #= env' "b" ] #= env' "object" :: S)
        assertEqual (banner r) e r
            
    , TestLabel "destructuring and unpacking statement" . TestCase $ do
        r <- parses program "[ { .x = .val } | rest ] = thing"
        let e = pure (setblock'' [ self' "x" #= self' "val" ] (env' "rest") #= env' "thing" :: S)
        assertEqual (banner r) e r
            
    , TestLabel "destructuring with multiple statements" . TestCase $ do
        r <- parses program "{ .x = .val; .z = priv } = other"
        let
          e = pure (setblock' [
            self' "x" #= self' "val", 
            self' "z" #= env' "priv"
            ] #= env' "other" :: S)
        assertEqual (banner r) e r
            
    , TestLabel "nested destructuring" . TestCase $ do
        r <- parses program "{ .x = .val; .y = { .z = priv } } = other"
        let
          e = pure (setblock' [
            self' "x" #= self' "val",
            self' "y" #= setblock' [ self' "z" #= env' "priv" ]
            ] #= env' "other" :: S)
        assertEqual (banner r) e r
        
    ]