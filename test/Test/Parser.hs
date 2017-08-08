module Test.Parser 
  ( tests
  ) where

import Types.Parser
import Types.Util.List
--import Types.Parser.Short
import qualified Types.Error as E
import Lib( readParser )
import Parser( program, rhs )

import Data.List.NonEmpty( NonEmpty(..) )
import Data.Function( (&) )
import Text.Parsec.String( Parser )
import Text.Parsec( ParseError )
import Test.HUnit
  ( Test(..)
  , Assertion(..)
  , assertEqual
  , assertFailure
  , assertBool
  )
  
  
banner :: String -> String
banner s = "For " ++ s ++ ","


parse :: Parser Rval -> String -> (ParseError -> Assertion) -> (Rval -> Assertion) -> Assertion
parse parser input err succ =
  either err succ (readParser parser input)


tests =
 TestList
    [ TestLabel "empty program" . TestCase $
        parse program ""
          (\ _ -> return ())
          (assertFailure . show)
    
    , TestLabel "string" . TestCase $
        parse rhs
          "\"hi\""
          (assertFailure . show)
          (assertEqual "" $ StringLit ("hi" :| []))
    
    , TestLabel "whitespace separated strings" . TestCase $
        parse rhs
          "\"one\" \"two\""
          (assertFailure . show)
          (assertEqual "" $ StringLit ("one" :| ["two"]))
    
    , TestLabel "number" . TestCase $
        parse rhs
          "123"
          (assertFailure . show)
          (assertEqual "" $ IntegerLit 123)
    
    , TestLabel "trailing decimal" . TestCase $
        parse rhs
          "123."
          (assertFailure . show)
          (assertEqual "" $ NumberLit 123)
    
    , TestLabel "decimal with trailing digits" . TestCase $
        parse rhs
          "123.0"
          (assertFailure . show)
          (assertEqual "" $ NumberLit 123)
        
    , TestLabel "underscores in number" . TestCase $
        parse rhs
          "1_000.2_5"
          (assertFailure . show)
          (assertEqual "" $ NumberLit 1000.25)
        
    , TestLabel "binary" . TestCase $
        parse rhs
          "0b100"
          (assertFailure . show)
          (assertEqual "" $ IntegerLit 4)
        
    , TestLabel "octal" . TestCase $ 
        parse rhs
          "0o11"
          (assertFailure . show)
          (assertEqual "" $ IntegerLit 9)
        
    , TestLabel "hexidecimal" . TestCase $
        parse rhs
          "0xa0"
          (assertFailure . show)
          (assertEqual "" $ IntegerLit 160)
        
    , TestLabel "plain identifier" . TestCase $
        parse rhs
          "name"
          (assertFailure . show)
          (assertEqual "" $ GetEnv (Field "name"))
        
    , TestLabel "period separated identifiers" . TestCase $
        parse rhs
          "path.to.thing"
          (assertFailure . show)
          (assertEqual "" $ 
            (GetEnv (Field "path")
              `Get` Field "to")
              `Get` Field "thing")
               
    , TestLabel "identifiers separated by period and space" . TestCase $
        parse rhs
          "with. space"
          (assertFailure . show)
          (assertEqual "" $ 
            GetEnv (Field "with")
              `Get` Field "space")
                
    , TestLabel "identifiers separated by space and period" . TestCase $
        parse rhs
          "with .space"
          (assertFailure . show)
          (assertEqual "" $ 
            GetEnv (Field "with")
              `Get` Field "space")
                
    , TestLabel "identifiers separaed by spaces around period" . TestCase $
        parse rhs
          "with . spaces"
          (assertFailure . show)
          (assertEqual "" $ 
            GetEnv (Field "with")
              `Get` Field "spaces")
                
    , TestLabel "identifier with  beginning period" . TestCase $
        parse rhs
          ".local" 
          (assertFailure . show)
          (assertEqual "" $ GetSelf (Field "local"))
          
    , TestLabel "brackets around identifier" . TestCase $
        parse rhs
          "(bracket)"
          (assertFailure . show)
          (assertEqual "" $ GetEnv (Field "bracket"))
          
    , TestLabel "empty brackets" . TestCase $
        parse rhs "()"
          (\ _ -> return ())
          (assertFailure . show)
          
    , TestLabel "identifier with applied brackets" . TestCase $
        parse rhs
          "a.thing(applied)"
          (assertFailure . show)
          (assertEqual "" $ 
            (GetEnv (Field "a")
              `Get` Field "thing")
              `Apply` GetEnv (Field "applied"))
             
    , TestLabel "identifier beginning with period with applied brackets" . TestCase $
        parse rhs
          ".local(applied)"
          (assertFailure . show)
          (assertEqual "" $ 
            GetSelf (Field "local")
              `Apply` GetEnv (Field "applied"))
             
    , TestLabel "chained applications" . TestCase $
        parse rhs
          ".thing(a).get(b)"
          (assertFailure . show)
          (assertEqual "" $ 
            ((GetSelf (Field "thing")
              `Apply` GetEnv (Field "a"))
              `Get` Field "get")
              `Apply` GetEnv (Field "b"))
             
    , TestLabel "primitive negative number" . TestCase $
        parse rhs
          "-45" 
          (assertFailure . show)
          (assertEqual "" $ Unop Neg (IntegerLit 45))
          
    , TestLabel "boolean not" . TestCase $
        parse rhs
          "!hi" 
          (assertFailure . show)
          (assertEqual "" $ Unop Not (GetEnv (Field "hi")))
          
    , TestLabel "boolean and" . TestCase $
        parse rhs
          "this & that"
          (assertFailure . show)
          (assertEqual "" $ GetEnv (Field "this")
            & Binop And $ GetEnv (Field "that"))
             
    , TestLabel "boolean or" . TestCase $
        parse rhs
          "4 | 2" 
          (assertFailure . show)
          (assertEqual "" $ IntegerLit 4
            & Binop Or $ IntegerLit 2)
             
    , TestLabel "addition" . TestCase $
        parse rhs
          "10 + 3"
          (assertFailure . show)
          (assertEqual "" $ IntegerLit 10
            & Binop Add $ IntegerLit 3)
             
    , TestLabel "multiple additions" . TestCase $
        parse rhs
          "a + b + c"
          (assertFailure . show)
          (assertEqual "" $ (GetEnv (Field "a")
            & Binop Add $ GetEnv (Field "b"))
            & Binop Add $ GetEnv (Field "c"))
              
    , TestLabel "subtration" . TestCase $
        parse rhs
          "a - b" 
          (assertFailure . show)
          (assertEqual "" $ GetEnv (Field "a") 
            & Binop Sub $ GetEnv (Field "b"))
             
    , TestLabel "mixed addition and subtraction" . TestCase $
        parse rhs
          "a + b - c"
          (assertFailure . show)
          (assertEqual "" $ (GetEnv (Field "a")
            & Binop Add $ GetEnv (Field "b"))
            & Binop Sub $ GetEnv (Field "c"))
            
    , TestLabel "multiplication" . TestCase $
        parse rhs
          "a * 2" 
          (assertFailure . show)
          (assertEqual "" $ GetEnv (Field "a")
            & Binop Prod $ IntegerLit 2)
             
    , TestLabel "division" . TestCase $
        parse rhs
          "value / 2"
          (assertFailure . show)
          (assertEqual "" $ GetEnv (Field "value")
            & Binop Div $ IntegerLit 2)
             
    , TestLabel "power" . TestCase $
        parse rhs
          "3^i" 
          (assertFailure . show)
          (assertEqual "" $
            IntegerLit 3
              & Binop Pow $ GetEnv (Field "i"))
             
    , TestLabel "comparisons"
        (TestList
          [ TestCase $
              parse rhs
                "3 > 2" 
                (assertFailure . show)
                (assertEqual "" $
                  IntegerLit 3
                    & Binop Gt $ IntegerLit 2)
                  
          , TestCase $
              parse rhs
                "2 < abc"
                (assertFailure . show)
                (assertEqual "" $
                  IntegerLit 2
                    & Binop Lt $ GetEnv (Field "abc"))
                
          , TestCase $
              parse rhs
                "a <= b"
                (assertFailure . show)
                (assertEqual "" $
                  GetEnv (Field "a")
                    & Binop Le $ GetEnv (Field "b"))
                  
          , TestCase $
              parse rhs
                "b >= 4"
                (assertFailure . show)
                (assertEqual "" $
                  GetEnv (Field "b")
                    & Binop Ge $
                      IntegerLit 4)
                  
          , TestCase $
              parse rhs
                "2 == True"
                (assertFailure . show)
                (assertEqual "" $
                  IntegerLit 2
                    & Binop Eq $
                      GetEnv (Field "True"))
                  
          , TestCase $
              parse rhs
                "3 != 3"
                (assertFailure . show)
                (assertEqual "" $
                  IntegerLit 3
                    & Binop Ne $ IntegerLit 3)
                  
          ])
           
    , TestLabel "mixed numeric and boolean operations" . TestCase $
        parse rhs
          "1 + 1 + 3 & 5 - 1"
          (assertFailure . show)
          (assertEqual "" $ 
            ((IntegerLit 1
              & Binop Add $ IntegerLit 1)
              & Binop Add $ IntegerLit 3)
              & Binop And $
                (IntegerLit 5
                  & Binop Sub $ IntegerLit 1))
                
    , TestLabel "mixed addition, subtration and multiplication" . TestCase $
        parse rhs
          "1 + 1 + 3 * 5 - 1"
          (assertFailure . show)
          (assertEqual "" $ 
            ((IntegerLit 1
              & Binop Add $ IntegerLit 1)
              & Binop Add $
                (IntegerLit 3
                  & Binop Prod $ IntegerLit 5))
              & Binop Sub $ IntegerLit 1)
            
    , TestLabel "assignment" . TestCase $
        parse program
          "assign = 1" 
          (assertFailure . show)
          (assertEqual "" $ Structure
            ([ Address (InEnv (Field "assign"))
                `Set` IntegerLit 1 ]
            :<: Nothing))
            
    , TestLabel "assign zero" . TestCase $
        parse program
          "assign = 0"
          (assertFailure . show)
          (assertEqual "" $ Structure
            ([ Address (InEnv (Field "assign"))
                `Set` IntegerLit 0 ]
            :<: Nothing))
             
    , TestLabel "declare" . TestCase $
        parse program
          "undef ="
          (assertFailure . show)
          (assertEqual "" $ Structure
            ([ Declare (InEnv (Field "undef")) ]
            :<: Nothing))
             
    , TestLabel "object with assignment" .  TestCase $
        parse rhs
          "{ a = b }" 
          (assertFailure . show)
          (assertEqual "" $ Structure
            ([ Address (InEnv (Field "a")) 
                `Set` GetEnv (Field "b") ]
            :<: Nothing))
                   
    , TestLabel "object with multiple statements" . TestCase $
        parse rhs
        "{ a = 1; b = a; c }" 
        (assertFailure . show)
        (assertEqual "" $ Structure
          ([ Address (InEnv (Field "a"))
              `Set` IntegerLit 1
                
          , Address (InEnv (Field  "b"))
              `Set` GetEnv (Field "a")
                
          , SetPun (InEnv (Field "c"))
          
          ] :<: Nothing))   
          
    , TestLabel "empty object" . TestCase $
        parse rhs "{}"
          (assertFailure . show)
          (assertEqual "" $ Structure ([] :<: Nothing))
        
    , TestLabel "object with run statement" . TestCase $
        parse rhs
          "{ #run a }"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([ Run (GetEnv (Field "a")) ]
              :<: Nothing))
            
    , TestLabel "object with pack statement" . TestCase $
        parse rhs
          "{ ...; #run .b }"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([] :<: Just (PackEnv :>:
                [ Run (GetSelf (Field "b")) ])))
        
    , TestLabel "destructuring assignment" . TestCase $
        parse program
          "{ .member = b } = object"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([ Destructure
                  ([] :<:
                    Right
                      ((AddressS . SelectSelf . Field) "member"
                        `As` 
                          (Address . InEnv . Field) "b"))
                  `Set` GetEnv (Field "object") ]
              :<: Nothing))
            
    , TestLabel "unpacked value" . TestCase $
        parse program
          "{...} = b" 
          (assertFailure . show)
          (assertEqual "" $
            Structure
              ([ Destructure
                  ([] :<: Left (UnpackRemaining :>: []))
                  `Set` GetEnv (Field "b") ]
              :<: Nothing))
            
    , TestLabel "destructuring with final unpack statement" . TestCase $
        parse program
          "{ .x = .val; ... } = thing"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([ Destructure
                  ([ (AddressS . SelectSelf . Field) "x"
                      `As` (Address . InSelf . Field) "val" ]
                  :<: 
                    Left
                      (UnpackRemaining :>: []))
                  `Set` GetEnv (Field "thing") ]
              :<: Nothing))
            
    , TestLabel "destructuring with beginning unpack statement" . TestCase $
        parse program
          "{ ...; .x = .out } = object"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([ Destructure
                  ([]
                  :<:
                    Left 
                      (UnpackRemaining :>:
                      [ (AddressS . SelectSelf . Field) "x"
                          `As` (Address . InSelf . Field) "out" ]))
                  `Set` GetEnv (Field "object") ]
              :<: Nothing))
            
    , TestLabel "destructuring with internal unpack statement" . TestCase $
        parse program
          "{ .x = .val; ...; .z = priv } = other"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([ Destructure
                  ([ (AddressS . SelectSelf . Field) "x"
                      `As`
                        (Address . InSelf . Field) "val" ]
                  :<:
                    Left 
                      (UnpackRemaining :>:
                      [ (AddressS . SelectSelf . Field) "z"
                        `As`
                          (Address . InEnv . Field) "priv" ]))
                  `Set`
                    GetEnv (Field "other") ]
              :<: Nothing))
            
    , TestLabel "destructuring with description statement" . TestCase $
        parse program
          "{ .x = .val; { .z = .y } = priv } = other"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([ Destructure
                  ([ (AddressS . SelectSelf . Field) "x"
                      `As`
                        (Address . InSelf . Field) "val" ]
                  :<:
                    Right 
                      (Description
                        (((Plain . AddressS . SelectSelf . Field) "z"
                          `Match`
                            (AddressS . SelectSelf . Field) "y")
                          :| [])
                        `As`
                          (Address . InEnv . Field) "priv"))
                  `Set`
                    GetEnv (Field "other") ]
              :<: Nothing))
            
    , TestLabel "destructuring with nested repack statement" . TestCase $
        parse program
          "{ .x = .val; { ...; .z = .y } = priv } = other"
          (assertFailure . show)
          (assertEqual "" $ 
            Structure
              ([ Destructure
                  ([ (AddressS . SelectSelf . Field) "x"
                        `As`
                          (Address . InSelf . Field) "val" ]
                  :<:
                    Left
                      ((DescriptionP
                        ([]
                        :<: RepackRemaining :>:
                         [ (Plain . AddressS . SelectSelf . Field) "z"
                              `Match`
                                (AddressS . SelectSelf . Field) "y" ])
                        `AsP`
                          (Address . InEnv . Field) "priv") 
                      :>: []))
                  `Set`
                    GetEnv (Field "other") ]
              :<: Nothing))
            
    ]