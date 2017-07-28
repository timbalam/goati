module Test.Parser 
  ( tests
  ) where

import Types.Parser
import qualified Types.Error as E
import Lib( readParser )
import Parser( program, rhs )

import Data.List.NonEmpty( NonEmpty(..) )
import Text.Parsec.String( Parser )
import Test.HUnit
  ( Test(..)
  , Assertion(..)
  , assertEqual
  , assertFailure
  , assertBool
  )
 
assertParse :: Parser Rval -> String -> Rval -> Assertion 
assertParse parser input expected =
  either
    (assertFailure . show)
    (assertEqual banner expected)
    (readParser parser input)
  where
    banner = "Parsing \"" ++ input ++ "\""
      
assertParseError :: Parser Rval -> String -> String -> Assertion
assertParseError parser msg input =
  either
    (\ _ -> return ())
    (\ res -> assertFailure (banner ++ "\nexpected " ++ msg ++ " but got: " ++ show res))
    (readParser parser input)
  where
    banner = "Parsing \"" ++ input ++ "\""
    
tests =
 TestList
    [ TestLabel "empty program" . TestCase $
        assertParseError program "empty program" ""
    
    , TestLabel "string" . TestCase $
        assertParse rhs "\"hi\"" (T.String "hi")
    
    , TestLabel "whitespace separated strings" . TestCase $
        assertParse rhs "\"one\" \"two\"" (T.String "onetwo")
    
    , TestLabel "number" . TestCase $
        assertParse rhs "123" (T.Number 123)
    
    , TestLabel "trailing decimal" . TestCase $
        assertParse rhs "123." (T.Number 123)
    
    , TestLabel "decimal with trailing digits" . TestCase $
        assertParse rhs "123.0" (T.Number 123)
        
    , TestLabel "underscores in number" . TestCase $
        assertParse rhs "1_000.2_5" (T.Number 1000.25)
        
    , TestLabel "binary" . TestCase $
        assertParse rhs "0b100" (T.Number 4)
        
    , TestLabel "octal" . TestCase $ 
        assertParse rhs "0o11" (T.Number 9)
        
    , TestLabel "hexidecimal" . TestCase $
        assertParse rhs "0xa0" (T.Number 160)
        
    , TestLabel "plain identifier" . TestCase $
        assertParse rhs "name" (T.Rident (T.Ident "name"))
        
    , TestLabel "period separated identifiers" . TestCase $
        assertParse rhs
          "path.to.thing"
          (T.Rroute 
            (T.Route
              (T.Rroute
                (T.Route
                  (T.Rident (T.Ident "path"))
                  (T.Ident "to")))
              (T.Ident "thing")))
               
    , TestLabel "identifiers separated by period and space" . TestCase $
        assertParse rhs
          "with. space"
          (T.Rroute
            (T.Route
              (T.Rident (T.Ident "with"))
              (T.Ident "space")))
                
    , TestLabel "identifiers separated by space and period" . TestCase $
        assertParse rhs
          "with .space"
          (T.Rroute
            (T.Route
              (T.Rident (T.Ident "with"))
              (T.Ident "space")))
                
    , TestLabel "identifiers separaed by spaces around period" . TestCase $
        assertParse rhs
          "with . spaces"
          (T.Rroute
            (T.Route
              (T.Rident (T.Ident "with"))
              (T.Ident "spaces")))
                
    , TestLabel "identifier with  beginning period" . TestCase $
        assertParse rhs
          ".local" 
          (T.Rroute (T.Atom (T.Ident "local")))
          
    , TestLabel "brackets around identifier" . TestCase $
        assertParse rhs
          "(bracket)"
          (T.Rident (T.Ident "bracket"))
          
    , TestLabel "empty brackets" . TestCase $
        assertParseError rhs
          "empty bracket"
          "()"
          
    , TestLabel "identifier with applied brackets" . TestCase $
        assertParse rhs
          "a.thing(applied)"
          (T.App
            (T.Rroute
              (T.Route
                (T.Rident (T.Ident "a"))
                (T.Ident "thing")))
            (T.Rident (T.Ident "applied")))
             
    , TestLabel "identifier beginning with period with applied brackets" . TestCase $
        assertParse rhs
          ".local(applied)"
          (T.App 
            (T.Rroute (T.Atom (T.Ident "local")))
            (T.Rident (T.Ident "applied")))
             
    , TestLabel "chained applications" . TestCase $
        assertParse rhs
          ".thing(a).get(b)"
          (T.App
            (T.Rroute
              (T.Route
                (T.App
                  (T.Rroute (T.Atom (T.Ident "thing")))
                  (T.Rident (T.Ident "a")))
                (T.Ident "get")))
            (T.Rident (T.Ident "b")))
             
    , TestLabel "primitive negative number" . TestCase $
        assertParse rhs
          "-45" 
          (T.Unop T.Neg (T.Number 45))
          
    , TestLabel "boolean not" . TestCase $
        assertParse rhs
          "!hi" 
          (T.Unop T.Not (T.Rident (T.Ident "hi")))
          
    , TestLabel "boolean and" . TestCase $
        assertParse rhs
          "this & that"
          (T.Binop T.And 
            (T.Rident (T.Ident "this"))
            (T.Rident (T.Ident "that")))
             
    , TestLabel "boolean or" . TestCase $
        assertParse rhs
          "4 | 2" 
          (T.Binop T.Or
            (T.Number 4)
            (T.Number 2))
             
    , TestLabel "addition" . TestCase $
        assertParse rhs
          "10 + 3"
          (T.Binop T.Add
            (T.Number 10)
            (T.Number 3))
             
    , TestLabel "multiple additions" . TestCase $
        assertParse rhs
          "a + b + c"
          (T.Binop T.Add
            (T.Binop T.Add
              (T.Rident (T.Ident "a"))
              (T.Rident (T.Ident "b")))
            (T.Rident (T.Ident "c")))
              
    , TestLabel "subtration" . TestCase $
        assertParse rhs
          "a - b" 
          (T.Binop T.Sub
            (T.Rident (T.Ident "a"))
            (T.Rident (T.Ident "b")))
             
    , TestLabel "mixed addition and subtraction" . TestCase $
        assertParse rhs
          "a + b - c"
          (T.Binop T.Sub
            (T.Binop T.Add
              (T.Rident (T.Ident "a"))
              (T.Rident (T.Ident "b")))
            (T.Rident (T.Ident "c")))
            
    , TestLabel "multiplication" . TestCase $
        assertParse rhs
          "a * 2" 
          (T.Binop T.Prod
            (T.Rident (T.Ident "a"))
            (T.Number 2))
             
    , TestLabel "division" . TestCase $
        assertParse rhs
          "value / 2"
          (T.Binop T.Div
            (T.Rident (T.Ident "value"))
            (T.Number 2))
             
    , TestLabel "power" . TestCase $
        assertParse rhs
          "3^i" 
          (T.Binop T.Pow
            (T.Number 3)
            (T.Rident (T.Ident "i")))
             
    , TestLabel "comparisons"
        (TestList
          [ TestCase $
              assertParse rhs
                "3 > 2" 
                (T.Binop T.Gt
                  (T.Number 3)
                  (T.Number 2))
                  
          , TestCase $
              assertParse rhs
                "2 < abc"
                (T.Binop T.Lt
                  (T.Number 2)
                  (T.Rident (T.Ident "abc")))
                
          , TestCase $
              assertParse rhs
                "a <= b"
                (T.Binop T.Le
                  (T.Rident (T.Ident "a"))
                  (T.Rident (T.Ident "b")))
                  
          , TestCase $
              assertParse rhs
                "b >= 4"
                (T.Binop T.Ge
                  (T.Rident (T.Ident "b"))
                  (T.Number 4))
                  
          , TestCase $
              assertParse rhs
                "2 == True"
                (T.Binop T.Eq
                  (T.Number 2)
                  (T.Rident (T.Ident "True")))
                  
          , TestCase $
              assertParse rhs
                "3 != 3"
                (T.Binop T.Ne
                  (T.Number 3)
                  (T.Number 3))
                  
          ])
           
    , TestLabel "mixed numeric and boolean operations" . TestCase $
        assertParse rhs
          "1 + 1 + 3 & 5 - 1"
          (T.Binop T.And 
            (T.Binop T.Add
              (T.Binop T.Add
                (T.Number 1)
                (T.Number 1))
              (T.Number 3))
            (T.Binop T.Sub
              (T.Number 5)
              (T.Number 1)))
                
    , TestLabel "mixed addition, subtration and multiplication" . TestCase $
        assertParse rhs
          "1 + 1 + 3 * 5 - 1"
          (T.Binop T.Sub
            (T.Binop T.Add
              (T.Binop T.Add
                (T.Number 1)
                (T.Number 1))
              (T.Binop T.Prod
                (T.Number 3)
                (T.Number 5)))
            (T.Number 1))
            
    , TestLabel "assignment" . TestCase $
        assertParse program
          "assign = 1" 
          (T.Rnode
            [ T.Laddress (T.Lident (T.Ident "assign"))
                `T.Assign`
                  T.Number 1
                  
            ])
            
    , TestLabel "assign zero" . TestCase $
        assertParse program
          "assign = 0"
          (T.Rnode
            [ T.Laddress (T.Lident (T.Ident "assign"))
                `T.Assign`
                  T.Number 0
                  
            ])
             
    , TestLabel "declare" . TestCase $
        assertParse program
          "undef ="
          (T.Rnode
            [ T.Declare (T.Lident (T.Ident "undef")) ])
             
    , TestLabel "object with assignment" .  TestCase $
        assertParse rhs
          "{ a = b }" 
          (T.Rnode
            [ T.Laddress (T.Lident (T.Ident "a")) 
                `T.Assign`
                  T.Rident (T.Ident "b")
                  
            ])
                   
    , TestLabel "object with multiple statements" . TestCase $
        assertParse rhs
        "{ a = 1; b = a; c }" 
        (T.Rnode
          [ T.Laddress (T.Lident (T.Ident "a"))
              `T.Assign`
                T.Number 1
                
          , T.Laddress (T.Lident (T.Ident  "b"))
              `T.Assign`
                T.Rident (T.Ident "a")
                
          , T.Eval (T.Rident (T.Ident "c"))
          
          ])     
          
    , TestLabel "empty object" . TestCase $
        assertParse rhs "{}" (T.Rnode [])
        
    , TestLabel "destructuring assignment" . TestCase $
        assertParse program
          "{ .member = b } = object"
          (T.Rnode
            [ T.Lnode
                [ T.PlainRoute (T.Atom (T.Ident "member"))
                    `T.ReversibleAssign`
                      T.Laddress (T.Lident (T.Ident  "b")) ]
                `T.Assign` 
                  T.Rident (T.Ident "object")
            ])
            
    , TestLabel "unpacked value" . TestCase $
        assertParse program
          "*b" 
          (T.Rnode
            [ T.Unpack (T.Rident (T.Ident "b")) ])
            
    , TestLabel "destructuring with final unpack statement" . TestCase $
        assertParse program
          "{ .x = .val; *y } = thing"
          (T.Rnode
            [ T.Lnode
                [ T.PlainRoute (T.Atom (T.Ident "x"))
                    `T.ReversibleAssign`
                      (T.Laddress (T.Lroute (T.Atom (T.Ident "val"))))
                      
                , T.ReversibleUnpack (T.Laddress (T.Lident (T.Ident "y")))
                
                ]
                `T.Assign` (T.Rident (T.Ident "thing"))
                
            ])
            
    , TestLabel "destructuring with beginning unpack statement" . TestCase $
        assertParse program
          "{ *.y; .x = .out } = object"
          (T.Rnode
            [ T.Lnode
                [ T.ReversibleUnpack (T.Laddress (T.Lroute (T.Atom (T.Ident "y"))))
                
                , T.PlainRoute (T.Atom (T.Ident "x"))
                    `T.ReversibleAssign`
                      (T.Laddress (T.Lroute (T.Atom (T.Ident "out"))))
                      
                ]
                `T.Assign`
                  (T.Rident (T.Ident "object"))
                  
            ])
            
    , TestLabel "destructuring with internal unpack statement" . TestCase $
        assertParse program
          "{ .x = .val; *y; .z = priv } = other"
          (T.Rnode
            [ T.Lnode
                [ T.PlainRoute (T.Atom (T.Ident "x"))
                    `T.ReversibleAssign`
                      T.Laddress (T.Lroute (T.Atom (T.Ident "val")))
                
                , T.ReversibleUnpack (T.Laddress (T.Lident (T.Ident "y")))
                
                , T.PlainRoute (T.Atom (T.Ident "z"))
                    `T.ReversibleAssign`
                      T.Laddress (T.Lident (T.Ident "priv"))
                      
                ]
                `T.Assign`
                  (T.Rident (T.Ident "other"))
                  
            ])
            
    ]{-
       
    -}