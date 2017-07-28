{-# LANGUAGE FlexibleContexts #-}

module Test.Eval
  ( assertEval
  , tests
  )
  where

import Eval
  ( evalRval
  , runEval
  )
import Types.Eval
import Types.Parser
--import Types.Parser.Short
import qualified Types.Error as E
import Lib( readParser )
import Parser( program, rhs )

import Control.Monad.IO.Class( liftIO )
import Control.Monad.Reader ( runReaderT )
import Control.Exception
import Data.Function( (&), ($) )
import Test.HUnit
  ( Test(..)
  , Assertion
  , assertEqual
  , assertFailure
  , assertBool
  )
  
  
(<#) = (&)
(#>) = ($)
  
  
assertEval :: Rval -> Value -> Assertion
assertEval r expected =
  do
    primEnv <- primitiveBindings
    v <- runEval (evalRval r) (primEnv, emptyEnv)
    assertEqual banner expected v
  where
    banner =
      "Evaluatiing \"" ++ show r ++ "\""

    
assertError :: Exception e => String -> Rval -> (e -> Bool) -> Assertion
assertError msg r test =
  catch
    (do
      primEnv <- primitiveBindings
      v <- runEval (evalRval r) (primEnv, emptyEnv)
      unexpected msg v)
    (\ e -> if test e then return () else unexpected msg e)
  where
    
    
    banner =
      "Evaluating \"" ++ show r ++ "\"" 
    
    
    unexpected msg v =
      assertFailure (banner ++ "\nexpected: " ++ msg ++ "\n but got: " ++ show v)

      
isUnboundVar :: String -> E.UnboundVar FieldId -> Bool
isUnboundVar a (E.UnboundVar (Field b) _) = a == b
    
    
tests =
  TestList
    [ TestLabel "add" . TestCase $
        assertEval
          (NumberLit 1 & Binop Add $ NumberLit 1)
          (Number 2)
          
    , TestLabel "subtract" . TestCase $
        assertEval
          (NumberLit 1 & Binop Sub $ NumberLit 2)
          (Number (-1))
          
    , TestLabel "public variable" . TestCase $
        assertEval
          (Structure
            [ Address (InSelf (Field "pub"))
                `Set` NumberLit 1 ]
            `Get` Field "pub")
          (Number 1)
          
    , TestLabel "private variable" . TestCase $ 
        assertError
          "Unbound var: priv"
          (Structure
            [ Address (InEnv (Field "priv"))
                `Set` NumberLit 1 ]
            `Get` Field "priv")
          (isUnboundVar "priv")
          
    , TestLabel "private variable access backward" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "priv"))
                `Set` NumberLit 1
            
            , Address (InSelf (Field "pub"))
                `Set` GetEnv (Field "priv")
            
            ]
            `Get` Field "pub")
          (Number 1)
          
    , TestLabel "private variable access forward" . TestCase $
        assertEval
          (Structure
            [ Address (InSelf (Field "pub"))
                `Set` GetEnv (Field "priv")
            
            , Address (InEnv (Field "priv"))
                `Set` NumberLit 1
            
            ]
            `Get` Field "pub")
          (Number 1)
          
    , TestLabel "private access of public variable" . TestCase $
        assertEval
          (Structure
            [ Address (InSelf (Field "a"))
                `Set` NumberLit 1
            
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
                  
            ]
            `Get` Field "b")
          (Number 1)
          
    , TestLabel "private access in nested scope of public variable" . TestCase $
        assertEval
          (Structure
            [ Address (InSelf (Field "a"))
                `Set` NumberLit 1
            
            , Address (InEnv (Field "object"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "b"))
                        `Set` GetEnv (Field "a")
                    ]
            
            , Address (InSelf (Field "c"))
                `Set`
                  (GetEnv (Field "object")
                    `Get` Field "b")
                  
            ]
            `Get` Field "c")
          (Number 1)
          
    , TestLabel "access backward public variable from same scope" . TestCase $
        assertEval
          (Structure
            [ Address (InSelf (Field "b"))
                `Set` NumberLit 2
                  
            , Address (InSelf (Field "a"))
                `Set` GetSelf (Field "b")
                
            ]
            `Get` Field "a")
          (Number 2)
          
    , TestLabel "access forward public variable from same scope" . TestCase $
        assertEval
          (Structure
            [ Address (InSelf (Field "a"))
                `Set` GetSelf (Field "b")
                  
            , Address (InSelf (Field "b"))
                `Set` NumberLit 2
            
            ]
            `Get` Field "a")
          (Number 2)
    , TestLabel "unbound variable" . TestCase $
        assertError
          "Unbound var: c"
          (Structure 
            [ Address (InSelf (Field "a"))
                `Set` NumberLit 2
           
            , Address (InSelf (Field "b"))
                `Set`
                  (GetEnv (Field "c") & Binop Add $ NumberLit 1)
            
            ]
            `Get` Field "b")
          (isUnboundVar "c")
          
    , TestLabel "undefined variable" . TestCase $
        let
          node = 
            Structure
              [ Declare (InSelf (Field  "a"))
              
              , Address (InSelf (Field "b"))
                  `Set` NumberLit 1
                    
              ]
        in
          do
            assertEval
              (node `Get` Field "b")
              (Number 1)

            assertError "Unbound var '.a'"
              (node `Get` Field "a")
              (isUnboundVar "a")
    
    , TestLabel "unset variable forwards" . TestCase $
        assertError
          "Unbound var: c"
          (Structure
            [ Address (InEnv (Field "c"))
                `Set` NumberLit 1
                
            , Address (InEnv (Field "b"))
                `Set`
                  Structure
                    [ Declare (InEnv (Field "c"))
                    
                    , Address (InSelf (Field "a"))
                        `Set` GetEnv (Field "c")
                    
                    ]
             , Address (InSelf (Field "ba"))
                `Set`
                  (GetEnv (Field "b")
                    `Get` Field "a")
            
            ]
            `Get` Field "ba")
          (isUnboundVar "c")
          
    , TestLabel "unset variable backwards" . TestCase $
        assertError
          "Unbound var: c"
          (Structure
            [ Address (InEnv (Field "c"))
                `Set` NumberLit 1
            
            , Address (InEnv (Field "b"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` GetEnv (Field "c")
                    
                    , Declare (InEnv (Field "c"))
                    
                    ]
            , Address (InSelf (Field "ba"))
                `Set`
                  (GetEnv (Field "b")
                    `Get` Field "a")
                  
            ]
            `Get`
              Field "ba")
          (isUnboundVar "c")
          
    , TestLabel "application  overriding public variable" . TestCase $
        assertEval
          ((Structure 
            [ Address (InSelf (Field "a"))
                `Set` NumberLit 2
            
            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a") & Binop Add $ NumberLit 1)
            
            ]
            `Apply`
              Structure
                [ Address (InSelf (Field "a"))
                    `Set` NumberLit 1 ])
            `Get` Field "b")
          (Number 2)
          
    , TestLabel "default definition forward" . TestCase $
        assertEval
          ((Structure
            [ Address (InSelf (Field "a"))
                `Set`
                  (GetSelf (Field "b") & Binop Sub $ NumberLit 1)
            
            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a") & Binop Add $ NumberLit 1)
            
            ]
            `Apply`
              Structure
                [ Address (InSelf (Field "b"))
                    `Set` NumberLit 2 ])
            `Get` Field "a")
          (Number 1)
          
    , TestLabel "default definition backward" . TestCase $
        assertEval
          ((Structure
            [ Address (InSelf (Field "a"))
                `Set`
                  (GetSelf (Field "b") & Binop Sub $ NumberLit 1)
            
            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a") & Binop Add $ NumberLit 1)
            
            ]
            `Apply`
              Structure
                [ Address (InSelf (Field "a"))
                    `Set` NumberLit 2 ])
            `Get` Field "b")
          (Number 3)
          
    , TestLabel "route getter" . TestCase $
        assertEval
          ((Structure
            [ Address (InSelf (Field "a"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "aa"))
                        `Set` NumberLit 2 ]
            
            ]
            `Get` Field "a")
            `Get` Field "aa")
          (Number 2)
          
    , TestLabel "route setter" . TestCase $
        assertEval
          ((Structure
            [ Address (InSelf (Field  "a") `In` Field "aa")
                `Set` NumberLit 2 ]
            `Get` Field "a")
            `Get` Field "aa")
          (Number 2)
          
    , TestLabel "application overriding nested property" . TestCase $
        assertEval
          ((Structure
            [ Address (InSelf (Field "a"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "aa"))
                        `Set` NumberLit 0 ]
            
            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a")
                    `Get` Field "aa")

            ]
            `Apply`
              Structure
                [ Address (InSelf (Field  "a") `In` Field "aa")
                    `Set` NumberLit 1 ])
            `Get` Field "b")
          (Number 1)
          
    , TestLabel "shadowing update" . TestCase $
        assertEval
          ((Structure
            [ Address (InEnv (Field "outer"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    
            , Address (InSelf (Field "inner"))
                `Set`
                  Structure
                    [ Address (InEnv (Field "outer") `In` Field "b")
                        `Set` NumberLit 2
                  
                    , Address (InSelf (Field "ab"))
                        `Set` 
                          ((GetEnv (Field "outer") `Get` Field "a")
                            & Binop Add $
                              (GetEnv (Field "outer") `Get` Field "b"))
                              
                    ]
                      
            ]
            `Get` Field "inner")
            `Get` Field "ab")
          (Number 3)
          
    , TestLabel "shadowing update 2" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "outer"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 2
                    
                    , Address (InSelf (Field "b"))
                        `Set` NumberLit 1
                   
                    ]
                    
            , Address (InSelf (Field "inner"))
                `Set`
                  Structure
                    [ Address (InSelf (Field  "outer") `In` Field "b")
                        `Set` NumberLit 2 ]
                    
            , Address (InSelf (Field "ab"))
                `Set`
                  ((GetEnv (Field "outer") `Get` Field "a")
                    & Binop Add $
                      (GetEnv (Field "outer") `Get` Field "b"))
                      
            ]
            `Get` Field "ab")
          (Number 3)
          
    , TestLabel "destructuring" . TestCase $
        let
          rnode = 
            Structure
              [ Address (InEnv (Field "obj"))
                  `Set`
                    Structure
                      [ Address (InSelf (Field "a"))
                          `Set` NumberLit 2
                            
                      , Address (InSelf (Field "b"))
                          `Set` NumberLit 3
                            
                      ]
                      
              , Destructure
                  [ SelectSelf (Field "a")
                      `As`
                        Address (InSelf (Field "da"))
                        
                  , SelectSelf (Field "b")
                      `As`
                        Address (InSelf (Field "db"))
                        
                  ]
                  `Set` GetEnv (Field "obj")
              
              ]
        in
          do
            assertEval
              (rnode `Get` Field "da")
              (Number 2)
                
            assertEval
              (rnode `Get` Field "db")
              (Number 3)
                
    , TestLabel "destructuring unpack" . TestCase $
        assertEval
          ((Structure
            [ Address (InEnv (Field "obj"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 2
                    
                    , Address (InSelf (Field "b"))
                        `Set` NumberLit 3
                    
                    ]
            , Destructure
                [ SelectSelf (Field "a")
                    `As`
                      Address (InSelf (Field "da"))
                      
                , RemainingAs (InSelf (Field "dobj"))
                
                ]
              `Set` GetEnv (Field "obj")
            
            ]
            `Get` Field "dobj")
            `Get` Field "b")
          (Number 3)
          
    , TestLabel "nested destructuring" . TestCase $
        let 
          rnode =
            Structure
              [ Address (InEnv (Field "y1"))
                  `Set`
                    Structure
                      [ Address (InSelf (Field "a"))
                          `Set`
                            Structure
                              [ Address (InSelf (Field "aa"))
                                  `Set` NumberLit 3
                              
                              , Address (InSelf (Field "ab"))
                                  `Set`
                                    Structure
                                      [ Address (InSelf (Field "aba"))
                                          `Set` NumberLit 4 ]
                                      
                              ]
                              
                      ]
                      
              , Destructure
                  [ (SelectSelf (Field "a") `Select` Field "aa")
                      `As`
                        Address (InSelf (Field "da"))
                        
                  , ((SelectSelf (Field "a")
                      `Select` Field "ab")
                      `Select` Field "aba")
                      `As`
                        Address (InSelf (Field "daba"))
                        
                  ]
                  `Set` GetEnv (Field "y1")
                    
              , Address (InSelf (Field "raba"))
                  `Set`
                    (((GetEnv (Field "y1")
                      `Get` Field "a")
                      `Get` Field "ab")
                      `Get` Field "aba")
                        
              ]
        in
          do
            assertEval
              (rnode `Get` Field "raba")
              (Number 4)
            
            assertEval
              (rnode `Get` Field "daba")
              (Number 4)
              
    , TestLabel "unpack visible publicly" . TestCase $
        let
          rnode =
            Structure
              [ Address (InEnv (Field "w1"))
                  `Set`
                    Structure
                      [ Address (InSelf (Field "a"))
                          `Set` NumberLit 1 ]
                          
              , Address (InSelf (Field "w2"))
                  `Set`
                    Structure
                      [ Address (InSelf (Field "b"))
                          `Set` GetSelf (Field "a")
                            
                      , Unpack (GetEnv (Field "w1"))
                      
                      ]
                      
              , Address (InSelf (Field "w3"))
                  `Set`
                    (GetSelf (Field "w2")
                      `Get` Field "a")
                    
              ]
        in
          do
            assertEval
              ((rnode `Get` Field "w2") `Get` Field "b")
              (Number 1)
              
            assertEval
              (rnode `Get` Field "w3")
              (Number 1)

    , TestLabel "unpack visible privately" . TestCase $
        assertEval
          ((Structure
            [ Address (InEnv (Field "w1"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                        
            , Address (InSelf (Field "w2"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "b"))
                        `Set` GetEnv (Field "a")
                          
                    , Unpack (GetEnv (Field "w1"))
                        
                    ]
                    
            ]
            `Get` Field "w2")
            `Get` Field "b")
          (Number 1)
          
    , TestLabel "local private variable unpack visible publicly  ##depreciated behaviour" . TestCase $
        assertEval 
          (Structure
            [ Address (InEnv (Field "w1"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    
            , Unpack (GetEnv (Field "w1"))
             
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
                
            ]
            `Get` Field "a")
          (Number 1)
    , TestLabel "local private variable unpack visible privately ##depreciated behaviour" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "w1"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    
            , Unpack (GetEnv (Field "w1"))
             
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
                  
            ]
            `Get` Field "b")
          (Number 1)
          
    , TestLabel "local public variable unpack visible publicly ##depreciated behaviour" . TestCase $
        assertEval 
          (Structure
            [ Address (InSelf (Field "w1"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
            
            , Unpack (GetSelf (Field "w1"))
            
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
            
            ]
            `Get` Field "a")
          (Number 1)
          
    , TestLabel "access member of object with local public variable unpack ##depreciated behaviour" . TestCase $
        assertEval 
          (Structure
            [ Address (InSelf (Field "w1"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    
            , Unpack (GetSelf (Field "w1"))
             
            , Address (InSelf (Field "b"))
                `Set` NumberLit 2
                  
            ]
            `Get` Field "b")
          (Number 2)
          
    , TestLabel "local public variable unpack visible privately ##depreciated behaviour" . TestCase $
        assertEval
          (Structure
            [ Address (InSelf (Field "w1"))
                `Set`
                  Structure 
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
            
            , Unpack (GetSelf (Field "w1"))

            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")

            ]
            `Get` Field "b")
          (Number 1)
          
    , TestLabel "parent scope binding" . TestCase $
        assertEval
          ((Structure
            [ Address (InSelf (Field "inner"))
                `Set` NumberLit 1
              
            , Address (InEnv (Field "parInner"))
                `Set` GetSelf (Field "inner")
            
            , Address (InSelf (Field "outer"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "inner"))
                        `Set` NumberLit 2
                          
                    , Address (InSelf (Field "a"))
                        `Set` GetEnv (Field "parInner")
                          
                    ]

            ]
            `Get` Field "outer")
            `Get` Field "a")
          (Number 1)
          
    , TestLabel "unpack scope binding" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "inner"))
                `Set`
                  Structure
                    [ Address (InEnv (Field "var"))
                        `Set` NumberLit 1
                    
                    , Address (InSelf (Field "innerVar"))
                        `Set` GetEnv (Field "var")
                    
                    ]
           
            , Address (InEnv (Field "outer"))
                `Set`
                  Structure
                    [ Address (InEnv (Field "var"))
                        `Set` NumberLit 2
                  
                    , Unpack (GetEnv (Field "inner"))
                    
                    ]
                    
            , Address (InSelf (Field "a"))
                `Set`
                  (GetEnv (Field "outer")
                    `Get` Field "innerVar")
            
            ]
            `Get` Field "a")
          (Number 1)
    , TestLabel "self referencing definition" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "y"))
                `Set`
                  Structure
                    [ Address (InSelf (Field "a"))
                        `Set`
                          (GetEnv (Field "y")
                            `Get` Field "b")
                    
                    , Address (InSelf (Field "b"))
                        `Set` NumberLit 1
                    
                    ]
                    
            , Address (InSelf (Field "z"))
                `Set`
                  (GetEnv (Field "y")
                    `Get` Field "a")
                      
            ]
            `Get` Field "z")
          (Number 1)
          
    , TestLabel "application to referenced outer scope" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "y"))
                `Set`
                  Structure 
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1
                    
                    , Address (InEnv (Field "b"))
                        `Set` NumberLit 2
                    
                    , Address (InSelf (Field "x"))
                        `Set`
                          Structure
                            [ Address (InSelf (Field "a"))
                                `Set` GetEnv (Field "b") ]
                            
                    ]
                    
            , Address (InSelf (Field "a"))
                `Set`
                  ((GetEnv (Field "y")
                    `Apply`
                      (GetEnv (Field "y")
                        `Get` Field "x"))
                    `Get` Field "a")
            
            ]
            `Get` Field "a")
          (Number 2)
          
    , TestLabel "application to nested object" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "y"))
                `Set`
                  Structure 
                    [ Address (InSelf (Field "a"))
                        `Set` NumberLit 1
                   
                    , Address (InSelf (Field "x"))
                        `Set`
                          Structure
                            [ Address (InSelf (Field "a"))
                                `Set` NumberLit 2
                            
                            , Declare (InSelf (Field "x"))
                            
                            ]
                    
                    ]
            
            , Address (InSelf (Field "a"))
                `Set`
                  (((GetEnv (Field "y")
                    `Get` Field "x")
                    `Apply`
                      GetEnv (Field "y"))
                    `Get` Field "a")
            
            ]
            `Get` Field "a")
          (Number 1)
          
    , TestLabel "run statement" . TestCase $
        assertEval
          (Structure
            [ Address (InEnv (Field "a"))
                `Set` NumberLit 1
            
            , Run (GetEnv (Field "a"))

            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")

            ]
            `Get` Field "b")
          (Number 1)
          
    , TestLabel "eval unbound variable" . TestCase $
        assertError
          "Unbound var: x" 
          (Structure
            [ Address (InEnv (Field  "a"))
                `Set` NumberLit 1
            
            , Run (GetEnv (Field "x"))

            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
            
            ]
            `Get` Field "b")
          (isUnboundVar "x")
          
    ]