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
import Data.Typeable
import Text.Parsec.String( Parser )
import Text.Parsec( ParseError )
import Control.Exception
import Test.HUnit
  ( Test(..)
  , Assertion(..)
  , assertEqual
  , assertFailure
  , assertBool
  )
  
  
banner :: String -> String
banner s = "For " ++ s ++ ","


data E = E String
  deriving (Show, Typeable)

instance Exception E where
  displayException (E msg) = msg


left :: Show b => Either a b -> IO a
left = either return (throwIO . E . show)

right :: Show a => Either a b -> IO b
right = either (throwIO . E . show) return
  
  
parses :: Parser Rval -> String -> IO Rval
parses parser input =
  either (throwIO . E . show) return (readParser parser input)
  

fails :: Parser Rval -> String -> Assertion
fails parser input =
  either (\ _ -> return ()) (assertFailure . show) (readParser parser input)
  


tests =
 TestList
    [ TestLabel "empty program" . TestCase $
        fails program ""
    
    , TestLabel "string" . TestCase $
        parses rhs
          "\"hi\""
          >>=
          (assertEqual "" $ StringLit ("hi" :| []))
    
    , TestLabel "whitespace separated strings" . TestCase $
        parses rhs
          "\"one\" \"two\""
          >>=
          (assertEqual "" $ StringLit ("one" :| ["two"]))
    
    , TestLabel "number" . TestCase $
        parses rhs
          "123"
          >>=
          (assertEqual "" $ IntegerLit 123)
    
    , TestLabel "trailing decimal" . TestCase $
        parses rhs
          "123."
          >>=
          (assertEqual "" $ NumberLit 123)
    
    , TestLabel "decimal with trailing digits" . TestCase $
        parses rhs
          "123.0"
          >>=
          (assertEqual "" $ NumberLit 123)
        
    , TestLabel "underscores in number" . TestCase $
        parses rhs
          "1_000.2_5"
          >>=
          (assertEqual "" $ NumberLit 1000.25)
        
    , TestLabel "binary" . TestCase $
        parses rhs
          "0b100"
          >>=
          (assertEqual "" $ IntegerLit 4)
        
    , TestLabel "octal" . TestCase $ 
        parses rhs
          "0o11"
          >>=
          (assertEqual "" $ IntegerLit 9)
        
    , TestLabel "hexidecimal" . TestCase $
        parses rhs
          "0xa0"
          >>=
          (assertEqual "" $ IntegerLit 160)
        
    , TestLabel "plain identifier" . TestCase $
        parses rhs
          "name"
          >>=
          (assertEqual "" $ GetEnv (Field "name"))
        
    , TestLabel "period separated identifiers" . TestCase $
        parses rhs
          "path.to.thing"
          >>=
          (assertEqual "" $ 
            (GetEnv (Field "path")
              `Get` Field "to")
              `Get` Field "thing")
               
    , TestLabel "identifiers separated by period and space" . TestCase $
        parses rhs
          "with. space"
          >>=
          (assertEqual "" $ 
            GetEnv (Field "with")
              `Get` Field "space")
                
    , TestLabel "identifiers separated by space and period" . TestCase $
        parses rhs
          "with .space"
          >>=
          (assertEqual "" $ 
            GetEnv (Field "with")
              `Get` Field "space")
                
    , TestLabel "identifiers separaed by spaces around period" . TestCase $
        parses rhs
          "with . spaces"
          >>=
          (assertEqual "" $ 
            GetEnv (Field "with")
              `Get` Field "spaces")
                
    , TestLabel "identifier with  beginning period" . TestCase $
        parses rhs
          ".local" 
          >>=
          (assertEqual "" $ GetSelf (Field "local"))
          
    , TestLabel "brackets around identifier" . TestCase $
        parses rhs
          "(bracket)"
          >>=
          (assertEqual "" $ GetEnv (Field "bracket"))
          
    , TestLabel "empty brackets" . TestCase $
        fails rhs "()"
          
    , TestLabel "identifier with applied brackets" . TestCase $
        parses rhs
          "a.thing(applied)"
          >>=
          (assertEqual "" $ 
            (GetEnv (Field "a")
              `Get` Field "thing")
              `Apply` GetEnv (Field "applied"))
             
    , TestLabel "identifier beginning with period with applied brackets" . TestCase $
        parses rhs
          ".local(applied)"
          >>=
          (assertEqual "" $ 
            GetSelf (Field "local")
              `Apply` GetEnv (Field "applied"))
             
    , TestLabel "chained applications" . TestCase $
        parses rhs
          ".thing(a).get(b)"
          >>=
          (assertEqual "" $ 
            ((GetSelf (Field "thing")
              `Apply` GetEnv (Field "a"))
              `Get` Field "get")
              `Apply` GetEnv (Field "b"))
             
    , TestLabel "primitive negative number" . TestCase $
        parses rhs
          "-45" 
          >>=
          (assertEqual "" $ Unop Neg (IntegerLit 45))
          
    , TestLabel "boolean not" . TestCase $
        parses rhs
          "!hi" 
          >>=
          (assertEqual "" $ Unop Not (GetEnv (Field "hi")))
          
    , TestLabel "boolean and" . TestCase $
        parses rhs
          "this & that"
          >>=
          (assertEqual "" $ GetEnv (Field "this")
            & Binop And $ GetEnv (Field "that"))
             
    , TestLabel "boolean or" . TestCase $
        parses rhs
          "4 | 2" 
          >>=
          (assertEqual "" $ IntegerLit 4
            & Binop Or $ IntegerLit 2)
             
    , TestLabel "addition" . TestCase $
        parses rhs
          "10 + 3"
          >>=
          (assertEqual "" $ IntegerLit 10
            & Binop Add $ IntegerLit 3)
             
    , TestLabel "multiple additions" . TestCase $
        parses rhs
          "a + b + c"
          >>=
          (assertEqual "" $ (GetEnv (Field "a")
            & Binop Add $ GetEnv (Field "b"))
            & Binop Add $ GetEnv (Field "c"))
              
    , TestLabel "subtration" . TestCase $
        parses rhs
          "a - b" 
          >>=
          (assertEqual "" $ GetEnv (Field "a") 
            & Binop Sub $ GetEnv (Field "b"))
             
    , TestLabel "mixed addition and subtraction" . TestCase $
        parses rhs
          "a + b - c"
          >>=
          (assertEqual "" $ (GetEnv (Field "a")
            & Binop Add $ GetEnv (Field "b"))
            & Binop Sub $ GetEnv (Field "c"))
            
    , TestLabel "multiplication" . TestCase $
        parses rhs
          "a * 2" 
          >>=
          (assertEqual "" $ GetEnv (Field "a")
            & Binop Prod $ IntegerLit 2)
             
    , TestLabel "division" . TestCase $
        parses rhs
          "value / 2"
          >>=
          (assertEqual "" $ GetEnv (Field "value")
            & Binop Div $ IntegerLit 2)
             
    , TestLabel "power" . TestCase $
        parses rhs
          "3^i" 
          >>=
          (assertEqual "" $
            IntegerLit 3
              & Binop Pow $ GetEnv (Field "i"))
             
    , TestLabel "comparisons"
        (TestList
          [ TestCase $
              parses rhs
                "3 > 2" 
                >>=
                (assertEqual "" $
                  IntegerLit 3
                    & Binop Gt $ IntegerLit 2)
                  
          , TestCase $
              parses rhs
                "2 < abc"
                >>=
                (assertEqual "" $
                  IntegerLit 2
                    & Binop Lt $ GetEnv (Field "abc"))
                
          , TestCase $
              parses rhs
                "a <= b"
                >>=
                (assertEqual "" $
                  GetEnv (Field "a")
                    & Binop Le $ GetEnv (Field "b"))
                  
          , TestCase $
              parses rhs
                "b >= 4"
                >>=
                (assertEqual "" $
                  GetEnv (Field "b")
                    & Binop Ge $
                      IntegerLit 4)
                  
          , TestCase $
              parses rhs
                "2 == True"
                >>=
                (assertEqual "" $
                  IntegerLit 2
                    & Binop Eq $
                      GetEnv (Field "True"))
                  
          , TestCase $
              parses rhs
                "3 != 3"
                >>=
                (assertEqual "" $
                  IntegerLit 3
                    & Binop Ne $ IntegerLit 3)
                  
          ])
           
    , TestLabel "mixed numeric and boolean operations" . TestCase $
        parses rhs
          "1 + 1 + 3 & 5 - 1"
          >>=
          (assertEqual "" $ 
            ((IntegerLit 1
              & Binop Add $ IntegerLit 1)
              & Binop Add $ IntegerLit 3)
              & Binop And $
                (IntegerLit 5
                  & Binop Sub $ IntegerLit 1))
                
    , TestLabel "mixed addition, subtration and multiplication" . TestCase $
        parses rhs
          "1 + 1 + 3 * 5 - 1"
          >>=
          (assertEqual "" $ 
            ((IntegerLit 1
              & Binop Add $ IntegerLit 1)
              & Binop Add $
                (IntegerLit 3
                  & Binop Prod $ IntegerLit 5))
              & Binop Sub $ IntegerLit 1)
            
    , TestLabel "assignment" . TestCase $
        parses program
          "assign = 1" 
          >>=
          (assertEqual "" $ Structure
            ([ Address (InEnv (Field "assign"))
                `Set` IntegerLit 1 ]
            :<: Nothing))
            
    , TestLabel "assign zero" . TestCase $
        parses program
          "assign = 0"
          >>=
          (assertEqual "" $ Structure
            ([ Address (InEnv (Field "assign"))
                `Set` IntegerLit 0 ]
            :<: Nothing))
             
    , TestLabel "declare" . TestCase $
        parses program
          "undef ="
          >>=
          (assertEqual "" $ Structure
            ([ Declare (InEnv (Field "undef")) ]
            :<: Nothing))
             
    , TestLabel "object with assignment" .  TestCase $
        parses rhs
          "{ a = b }" 
          >>=
          (assertEqual "" $ Structure
            ([ Address (InEnv (Field "a")) 
                `Set` GetEnv (Field "b") ]
            :<: Nothing))
                   
    , TestLabel "object with multiple statements" . TestCase $
        parses rhs
        "{ a = 1; b = a; c }" 
        >>=
        (assertEqual "" $ Structure
          ([ Address (InEnv (Field "a"))
              `Set` IntegerLit 1
                
          , Address (InEnv (Field  "b"))
              `Set` GetEnv (Field "a")
                
          , SetPun (InEnv (Field "c"))
          
          ] :<: Nothing))   
          
    , TestLabel "empty object" . TestCase $
        parses rhs "{}"
          >>=
          (assertEqual "" $ Structure ([] :<: Nothing))
        
    , TestLabel "object with run statement" . TestCase $
        parses rhs
          "{ #run a }"
          >>=
          (assertEqual "" $ 
            Structure
              ([ Run (GetEnv (Field "a")) ]
              :<: Nothing))
            
    , TestLabel "object with pack statement" . TestCase $
        parses rhs
          "{ ...; #run .b }"
          >>=
          (assertEqual "" $ 
            Structure
              ([] :<: Just (PackEnv :>:
                [ Run (GetSelf (Field "b")) ])))
        
    , TestLabel "destructuring assignment" . TestCase $
        parses program
          "{ .member = b } = object"
          >>=
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
        parses program
          "{...} = b" 
          >>=
          (assertEqual "" $
            Structure
              ([ Destructure
                  ([] :<: Left (UnpackRemaining :>: []))
                  `Set` GetEnv (Field "b") ]
              :<: Nothing))
            
    , TestLabel "destructuring with final unpack statement" . TestCase $
        parses program
          "{ .x = .val; ... } = thing"
          >>=
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
        parses program
          "{ ...; .x = .out } = object"
          >>=
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
        parses program
          "{ .x = .val; ...; .z = priv } = other"
          >>=
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
        parses program
          "{ .x = .val; { .z = .y } = priv } = other"
          >>=
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
        parses program
          "{ .x = .val; { ...; .z = .y } = priv } = other"
          >>=
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