module Test.Parser 
  ( tests
  ) where

import Types.Parser
import qualified Types.Error as E
import Lib( readParser )
import Parser( program, rhs )

import Data.Function( (&) )
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
  case readParser parser input of
    Left e -> 
      assertFailure (show e)
      
    Right r ->
      assertEqual banner expected r
      
  where
    banner = "Parsing \"" ++ input ++ "\""
      
assertParseError :: Parser Rval -> String -> String -> Assertion
assertParseError parser msg input =
  case readParser parser input of
    Left _ ->
      return ()
    
    Right r ->
      assertFailure
        (banner ++ "\nexpected " ++ msg ++ " but got: " ++ show r)
        
  where
    banner = "Parsing \"" ++ input ++ "\""
    
    
tests =
 TestList
    [ TestLabel "empty program" . TestCase $
        assertParseError program
          "empty program"
          ""
    
    , TestLabel "string" . TestCase $
        assertParse rhs
          "\"hi\""
          (StringLit "hi")
    
    , TestLabel "whitespace separated strings" . TestCase $
        assertParse rhs
          "\"one\" \"two\""
          (StringLit "onetwo")
    
    , TestLabel "number" . TestCase $
        assertParse rhs
          "123"
          (NumberLit 123)
    
    , TestLabel "trailing decimal" . TestCase $
        assertParse rhs
          "123."
          (NumberLit 123)
    
    , TestLabel "decimal with trailing digits" . TestCase $
        assertParse rhs
          "123.0"
          (NumberLit 123)
        
    , TestLabel "underscores in number" . TestCase $
        assertParse rhs
          "1_000.2_5"
          (NumberLit 1000.25)
        
    , TestLabel "binary" . TestCase $
        assertParse rhs
          "0b100"
          (NumberLit 4)
        
    , TestLabel "octal" . TestCase $ 
        assertParse rhs
          "0o11"
          (NumberLit 9)
        
    , TestLabel "hexidecimal" . TestCase $
        assertParse rhs
          "0xa0"
          (NumberLit 160)
        
    , TestLabel "plain identifier" . TestCase $
        assertParse rhs
          "name"
          (GetEnv (Field "name"))
        
    , TestLabel "period separated identifiers" . TestCase $
        assertParse rhs
          "path.to.thing"
          ((GetEnv (Field "path")
            `Get` Field "to")
            `Get` Field "thing")
               
    , TestLabel "identifiers separated by period and space" . TestCase $
        assertParse rhs
          "with. space"
          (GetEnv (Field "with")
            `Get` Field "space")
                
    , TestLabel "identifiers separated by space and period" . TestCase $
        assertParse rhs
          "with .space"
          (GetEnv (Field "with")
            `Get` Field "space")
                
    , TestLabel "identifiers separaed by spaces around period" . TestCase $
        assertParse rhs
          "with . spaces"
          (GetEnv (Field "with")
            `Get` Field "spaces")
                
    , TestLabel "identifier with  beginning period" . TestCase $
        assertParse rhs
          ".local" 
          (GetSelf (Field "local"))
          
    , TestLabel "brackets around identifier" . TestCase $
        assertParse rhs
          "(bracket)"
          (GetEnv (Field "bracket"))
          
    , TestLabel "empty brackets" . TestCase $
        assertParseError rhs
          "empty bracket"
          "()"
          
    , TestLabel "identifier with applied brackets" . TestCase $
        assertParse rhs
          "a.thing(applied)"
          ((GetEnv (Field "a")
            `Get` Field "thing")
            `Apply` GetEnv (Field "applied"))
             
    , TestLabel "identifier beginning with period with applied brackets" . TestCase $
        assertParse rhs
          ".local(applied)"
          (GetSelf (Field "local")
            `Apply` GetEnv (Field "applied"))
             
    , TestLabel "chained applications" . TestCase $
        assertParse rhs
          ".thing(a).get(b)"
          (((GetSelf (Field "thing")
            `Apply` GetEnv (Field "a"))
            `Get` Field "get")
            `Apply` GetEnv (Field "b"))
             
    , TestLabel "primitive negative number" . TestCase $
        assertParse rhs
          "-45" 
          (Unop Neg (NumberLit 45))
          
    , TestLabel "boolean not" . TestCase $
        assertParse rhs
          "!hi" 
          (Unop Not (GetEnv (Field "hi")))
          
    , TestLabel "boolean and" . TestCase $
        assertParse rhs
          "this & that"
          (GetEnv (Field "this")
            & Binop And $ GetEnv (Field "that"))
             
    , TestLabel "boolean or" . TestCase $
        assertParse rhs
          "4 | 2" 
          (NumberLit 4 & Binop Or $ NumberLit 2)
             
    , TestLabel "addition" . TestCase $
        assertParse rhs
          "10 + 3"
          (NumberLit 10
            & Binop Add $ NumberLit 3)
             
    , TestLabel "multiple additions" . TestCase $
        assertParse rhs
          "a + b + c"
          ((GetEnv (Field "a")
            & Binop Add $ GetEnv (Field "b"))
            & Binop Add $ GetEnv (Field "c"))
              
    , TestLabel "subtration" . TestCase $
        assertParse rhs
          "a - b" 
          (GetEnv (Field "a")
            & Binop Sub $ GetEnv (Field "b"))
             
    , TestLabel "mixed addition and subtraction" . TestCase $
        assertParse rhs
          "a + b - c"
          ((GetEnv (Field "a")
            & Binop Add $ GetEnv (Field "b"))
            & Binop Sub $ GetEnv (Field "c"))
            
    , TestLabel "multiplication" . TestCase $
        assertParse rhs
          "a * 2" 
          (GetEnv (Field "a")
            & Binop Prod $ NumberLit 2)
             
    , TestLabel "division" . TestCase $
        assertParse rhs
          "value / 2"
          (GetEnv (Field "value")
            & Binop Div $ NumberLit 2)
             
    , TestLabel "power" . TestCase $
        assertParse rhs
          "3^i" 
          (NumberLit 3
            & Binop Pow $ GetEnv (Field "i"))
             
    , TestLabel "comparisons"
        (TestList
          [ TestCase $
              assertParse rhs
                "3 > 2" 
                (NumberLit 3
                  & Binop Gt $ NumberLit 2)
                  
          , TestCase $
              assertParse rhs
                "2 < abc"
                (NumberLit 2
                  & Binop Lt $ GetEnv (Field "abc"))
                
          , TestCase $
              assertParse rhs
                "a <= b"
                (GetEnv (Field "a")
                  & Binop Le $ GetEnv (Field "b"))
                  
          , TestCase $
              assertParse rhs
                "b >= 4"
                (GetEnv (Field "b")
                  & Binop Ge $ NumberLit 4)
                  
          , TestCase $
              assertParse rhs
                "2 == True"
                (NumberLit 2
                  & Binop Eq $ GetEnv (Field "True"))
                  
          , TestCase $
              assertParse rhs
                "3 != 3"
                (NumberLit 3
                  & Binop Ne $ NumberLit 3)
                  
          ])
           
    , TestLabel "mixed numeric and boolean operations" . TestCase $
        assertParse rhs
          "1 + 1 + 3 & 5 - 1"
          (((NumberLit 1 
            & Binop Add $ NumberLit 1)
            & Binop Add $ NumberLit 3)
            & Binop And $
              (NumberLit 5
                & Binop Sub $ NumberLit 1))
                
    , TestLabel "mixed addition, subtration and multiplication" . TestCase $
        assertParse rhs
          "1 + 1 + 3 * 5 - 1"
          (((NumberLit 1
            & Binop Add $ NumberLit 1)
            & Binop Add $
              (NumberLit 3
                & Binop Prod $ NumberLit 5))
            & Binop Sub $ NumberLit 1)
            
    , TestLabel "assignment" . TestCase $
        assertParse program
          "assign = 1" 
          (Structure
            [ Address (InEnv (Field "assign"))
                `Set` NumberLit 1 ])
            
    , TestLabel "assign zero" . TestCase $
        assertParse program
          "assign = 0"
          (Structure
            [ Address (InEnv (Field "assign"))
                `Set` NumberLit 0 ])
             
    , TestLabel "declare" . TestCase $
        assertParse program
          "undef ="
          (Structure
            [ Declare (InEnv (Field "undef")) ])
             
    , TestLabel "object with assignment" .  TestCase $
        assertParse rhs
          "{ a = b }" 
          (Structure
            [ Address (InEnv (Field "a")) 
                `Set` GetEnv (Field "b") ])
                   
    , TestLabel "object with multiple statements" . TestCase $
        assertParse rhs
        "{ a = 1; b = a; c }" 
        (Structure
          [ Address (InEnv (Field "a"))
              `Set` NumberLit 1
                
          , Address (InEnv (Field  "b"))
              `Set` GetEnv (Field "a")
                
          , Run (GetEnv (Field "c"))
          
          ])     
          
    , TestLabel "empty object" . TestCase $
        assertParse rhs
          "{}"
          (Structure [])
        
    , TestLabel "destructuring assignment" . TestCase $
        assertParse program
          "{ .member = b } = object"
          (Structure
            [ Destructure
                [ SelectSelf (Field "member")
                    `As`
                      Address (InEnv (Field  "b")) ]
                `Set` GetEnv (Field "object") ])
            
    , TestLabel "unpacked value" . TestCase $
        assertParse program
          "*b" 
          (Structure
            [ Unpack (GetEnv (Field "b")) ])
            
    , TestLabel "destructuring with final unpack statement" . TestCase $
        assertParse program
          "{ .x = .val; *y } = thing"
          (Structure
            [ Destructure
                [ SelectSelf (Field "x")
                    `As`
                      Address (InSelf (Field "val"))
                      
                , RemainingAs (InEnv (Field "y"))
                
                ]
                `Set` GetEnv (Field "thing")
                
            ])
            
    , TestLabel "destructuring with beginning unpack statement" . TestCase $
        assertParse program
          "{ *.y; .x = .out } = object"
          (Structure
            [ Destructure
                [ RemainingAs (InSelf (Field "y"))
                
                , SelectSelf (Field "x")
                    `As`
                      Address (InSelf (Field "out"))
                      
                ]
                `Set` GetEnv (Field "object")
                  
            ])
            
    , TestLabel "destructuring with internal unpack statement" . TestCase $
        assertParse program
          "{ .x = .val; *y; .z = priv } = other"
          (Structure
            [ Destructure
                [ SelectSelf (Field "x")
                    `As` Address (InSelf (Field "val"))
                
                , RemainingAs (InEnv (Field "y"))
                
                , SelectSelf (Field "z")
                    `As` Address (InEnv (Field "priv"))
                      
                ]
                `Set` GetEnv (Field "other") ])
            
    ]