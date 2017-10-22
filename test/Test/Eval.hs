{-# LANGUAGE FlexibleContexts #-}

module Test.Eval
  ( run
  , tests
  )
  where

import Eval
  ( evalRval
  , runEval
  )
import Types.Eval
import Types.Parser
--import Types.Util.List
--import Types.Parser.Short
import qualified Types.Error as E

import Control.Monad.IO.Class( liftIO )
import Control.Monad.Reader( runReaderT )
import Control.Exception
import Data.Function( (&) )
import Test.HUnit
  ( Test(..)
  , Assertion
  , assertEqual
  , assertFailure
  , assertBool
  )
  
  
banner :: Rval -> String
banner r = "For " ++ show r ++ ","
  
  
run :: Rval -> IO Value
run r =
  do
    primEnv <-
      primitiveBindings
    
    runEval (evalRval r) (primEnv, emptyEnv)

    
field :: E.UnboundVar FieldId -> String
field (E.UnboundVar (Field b) _) = b


tests =
  TestList
    [ TestLabel "add" . TestCase $
        let
          r =
            IntegerLit 1
              & Binop Add $ IntegerLit 1
        in 
          run r
            >>= assertEqual (banner r) (Number 2)
          
    , TestLabel "subtract" . TestCase $
        let 
          r = (NumberLit 1 
            & Binop Sub $ NumberLit 2)
        in 
          run r
            >>= assertEqual (banner r) (Number (-1))
          
    , TestLabel "public variable" . TestCase $
        run
          (Structure
            ([ Address (InSelf (Field "pub"))
                `Set` IntegerLit 1 ]
            :<: Nothing)
            `Get` Field "pub")
          >>=
          (assertEqual "" (Number 1))
          
    , TestLabel "private variable" . TestCase $ 
        catch
          (run
            (Structure
              ([ Address (InEnv (Field "priv"))
                  `Set` IntegerLit 1 ]
              :<: Nothing)
              `Get` Field "priv")
            >>= assertFailure . show)
          (assertEqual "Unbound var: priv" "priv" . field)
          
    , TestLabel "private variable access backward" . TestCase $
        run
          (Structure
            ([ Address (InEnv (Field "priv"))
                `Set` NumberLit 1
            
            , Address (InSelf (Field "pub"))
                `Set` GetEnv (Field "priv")
                
            ] :<: Nothing)
            `Get` Field "pub")
          >>=
          (assertEqual "" (Number 1))
          
    , TestLabel "private variable access forward" . TestCase $
        run
          (Structure
            ([ Address (InSelf (Field "pub"))
                `Set` GetEnv (Field "priv")
                
            , Address (InEnv (Field "priv"))
                `Set` IntegerLit 1
            
            ] :<: Nothing)
            `Get` Field "pub")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "private access of public variable" . TestCase $
        run
          (Structure
            ([ Address (InSelf (Field "a"))
                `Set` IntegerLit 1
                
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
                
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "private access in nested scope of public variable" . TestCase $
        run
          (Structure
            ([ Address (InSelf (Field "a"))
                `Set` IntegerLit 1
            
            , Address (InEnv (Field "object"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "b"))
                        `Set` GetEnv (Field "a") ]
                    :<: Nothing)
                        
            , Address (InSelf (Field "c"))
                `Set`
                  (GetEnv (Field "object")
                    `Get` Field "b")
            
            ] :<: Nothing)
            `Get` Field "c")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "access backward public variable from same scope" . TestCase $
        run
          (Structure
            ([ Address (InSelf (Field "b"))
                `Set` IntegerLit 2
           
            , Address (InSelf (Field "a"))
                `Set` GetSelf (Field "b")
                
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" $ Number 2)
          
    , TestLabel "access forward public variable from same scope" . TestCase $
        run
          (Structure
            ([ Address (InSelf (Field "a"))
                `Set` GetSelf (Field "b")
            
            , Address (InSelf (Field "b"))
                `Set` NumberLit 2
            
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" $ Number 2)
          
    , TestLabel "unbound variable" . TestCase $
        catch
          (run
            (Structure
              ([ Address (InSelf (Field "a"))
                  `Set` IntegerLit 2
                  
              , Address (InSelf (Field "b"))
                  `Set`
                    (GetEnv (Field "c")
                      & Binop Add $ IntegerLit 1)
                      
              ] :<: Nothing)
              `Get` Field "b")
            >>= assertFailure . show)
          (assertEqual "Unbound var: c" "c" . field)
          
    , TestLabel "undefined variable" . TestCase $
        let
          val =
            Structure
              ([ Declare (InSelf (Field "a"))
              
              , Address (InSelf (Field "b"))
                  `Set` IntegerLit 1
              
              ] :<: Nothing)
        in
          do
            run (val `Get` Field "b")
              >>=
              (assertEqual "" $ Number 1)
            
            catch
              (run 
                (val `Get` Field "a")
                >>= assertFailure . show)
              (assertEqual "Unbound var '.a'" "a" . field)
              
    , TestLabel "unset variable forwards" . TestCase $
        catch
          (run
            (Structure
              ([ Address (InEnv (Field "c"))
                  `Set` IntegerLit 1
              
              , Address (InEnv (Field "b"))
                  `Set`
                    Structure
                      ([ Declare (InEnv (Field "c"))
                      
                      , Address (InSelf (Field "a"))
                          `Set` GetEnv (Field "c")
                          
                      ] :<: Nothing)
               
              , Address (InSelf (Field "ba"))
                  `Set`
                    (GetEnv (Field "b")
                      `Get` Field "a")
              
              ] :<: Nothing)
              `Get` Field "ba")
            >>= assertFailure . show)
          (assertEqual "Unbound var: c" "c" . field)
          
    , TestLabel "unset variable backwards" . TestCase $
        catch
          (run
            (Structure
              ([ Address (InEnv (Field "c"))
                  `Set` IntegerLit 1
                  
              , Address (InEnv (Field "b"))
                  `Set`
                    Structure
                      ([ Address (InSelf (Field "a"))
                          `Set` GetEnv (Field "c")
                      
                      , Declare (InEnv (Field "c"))
                      
                      ] :<: Nothing)
                
              , Address (InSelf (Field "ba"))
                  `Set`
                    (GetEnv (Field "b")
                      `Get` Field "a")
              
              ] :<: Nothing)
              `Get` Field "ba")
              >>= assertFailure . show)
          (assertEqual "Unbound var: c" "c" . field)
          
    , TestLabel "application  overriding public variable" . TestCase $
        run
          ((Structure
            ([ Address (InSelf (Field "a"))
                `Set` NumberLit 2

            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a")
                    & Binop Add $ NumberLit 1)

            ] :<: Nothing)
            `Apply`
              Structure
                ([ Address (InSelf (Field "a"))
                    `Set` NumberLit 1 ]
                :<: Nothing))
            `Get` Field "b")
          >>=
          (assertEqual "" $ Number 2)
          
    , TestLabel "default definition forward" . TestCase $
        run
          ((Structure
            ([ Address (InSelf (Field "a"))
                `Set`
                  (GetSelf (Field "b")
                    & Binop Sub $ NumberLit 1)
            
            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a")
                    & Binop Add $ NumberLit 1)
            
            ] :<: Nothing)
            `Apply`
              Structure
                ([ Address (InSelf (Field "b"))
                    `Set` NumberLit 2 ]
                :<: Nothing))
            `Get` Field "a")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "default definition backward" . TestCase $
        run
          ((Structure
            ([ Address (InSelf (Field "a"))
                `Set`
                  (GetSelf (Field "b") 
                    & Binop Sub $ NumberLit 1)
            
            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a")
                    & Binop Add $ NumberLit 1)
            
            ] :<: Nothing)
            `Apply`
              Structure
                ([ Address (InSelf (Field "a"))
                    `Set` NumberLit 2 ]
                :<: Nothing))
            `Get` Field "b")
          >>=
          (assertEqual "" $ Number 3)
          
    , TestLabel "route getter" . TestCase $
        run
          ((Structure
            ([ Address (InSelf (Field "a"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "aa"))
                        `Set` NumberLit 2 ]
                    :<: Nothing)
            ] :<: Nothing)
            `Get` Field "a")
            `Get` Field "aa")
          >>=
          (assertEqual "" $ Number 2)
          
    , TestLabel "route setter" . TestCase $
        run
          ((Structure
            ([ Address (InSelf (Field "a") `In` Field "aa")
                `Set` NumberLit 2 ]
            :<: Nothing)
            `Get` Field "a")
            `Get` Field "aa")
          >>=
          (assertEqual "" $ Number 2)
          
    , TestLabel "application overriding nested property" . TestCase $
        run
          ((Structure
            ([ Address (InSelf (Field "a"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "aa"))
                        `Set` NumberLit 0 ]
                    :<: Nothing)
            
            , Address (InSelf (Field "b"))
                `Set`
                  (GetSelf (Field "a")
                    `Get` Field "aa")
            
            ] :<: Nothing)
            `Apply`
              Structure
                ([ Address 
                    (InSelf (Field "a")
                      `In` Field "aa")
                    `Set` NumberLit 1 ]
                :<: Nothing))
            `Get` Field "b")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "shadowing update" . TestCase $
        run
          ((Structure
            ([ Address (InEnv (Field "outer"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
            
            , Address (InSelf (Field "inner"))
                `Set`
                  Structure
                    ([ Address
                        (InEnv (Field "outer")
                          `In` Field "b")
                        `Set` NumberLit 2
                        
                    , Address (InSelf (Field "ab"))
                        `Set` 
                          ((GetEnv (Field "outer")
                            `Get` Field "a")
                            & Binop Add $
                              (GetEnv (Field "outer")
                                `Get` Field "b"))
                                
                    ] :<: Nothing)
                    
            ] :<: Nothing)
            `Get` Field "inner")
            `Get` Field "ab")
          >>=
          (assertEqual "" $ Number 3)
          
    , TestLabel "shadowing update 2" . TestCase $
        run
          (Structure
            ([ Address (InEnv (Field "outer"))
                `Set`
                  Structure 
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 2
                    
                    , Address (InSelf (Field "b"))
                        `Set` NumberLit 1
                    
                    ] :<: Nothing)
                    
            , Address (InSelf (Field "inner"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "outer") `In` Field "b")
                        `Set` NumberLit 2 ]
                    :<: Nothing)
                      
            , Address (InSelf (Field "ab"))
               `Set`
                  ((GetEnv (Field "outer") `Get` Field "a")
                    & Binop Add $ 
                      (GetEnv (Field "outer") `Get` Field "b"))
            
            ] :<: Nothing)
            `Get` Field "ab")
          >>=
          (assertEqual "" $ Number 3)
          
    , TestLabel "destructuring" . TestCase $
        let
          val = 
            Structure
              ([ Address (InEnv (Field "obj"))
                  `Set`
                    Structure
                      ([ Address (InSelf (Field "a"))
                          `Set` NumberLit 2
                          
                      , Address (InSelf (Field "b"))
                          `Set` NumberLit 3
                          
                      ] :<: Nothing)
                      
              , Destructure
                  ([ AddressS (SelectSelf (Field "a"))
                    `As` Address (InSelf (Field "da")) ]
                  :<: 
                    Right
                      (AddressS (SelectSelf (Field "b"))
                        `As` Address (InSelf (Field "db")))
                  )
                  `Set` GetEnv (Field "obj")
                  
              ] :<: Nothing)
        in
          do
            run (val `Get` Field "da")
              >>=
              (assertEqual "" $ Number 2)
            
            run (val `Get` Field "db")
              >>=
              (assertEqual "" $ Number 3)
            
    , TestLabel "destructuring unpack" . TestCase $
        run
          (Structure
            ([ Address (InEnv (Field "obj"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set` IntegerLit 2
                        
                    , Address (InSelf (Field "b"))
                        `Set` IntegerLit 3
                    
                    ] :<: Nothing)
                    
            , Destructure
                ([ AddressS (SelectSelf (Field "a"))
                    `As` Address (InSelf (Field "da")) ]
                :<: Left (UnpackRemaining :>: []))
                `Set` GetEnv (Field "obj")
                
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" $ Number 3)
          
    , TestLabel "nested destructuring" . TestCase $
        let 
          val =
            Structure
              ([ Address (InEnv (Field "y1"))
                  `Set`
                    Structure
                      ([ Address (InSelf (Field "a"))
                          `Set`
                            Structure
                              ([ Address (InSelf (Field "aa"))
                                  `Set` NumberLit 3
                              
                              , Address (InSelf (Field "ab"))
                                  `Set`
                                    Structure
                                      ([ Address (InSelf (Field "aba"))
                                        `Set` NumberLit 4 ]
                                      :<: Nothing)
                            
                              ] :<: Nothing)
                      ] :<: Nothing)
                      
              , Destructure
                  ([ AddressS
                      (SelectSelf (Field "a")
                        `Select` Field "aa")
                      `As` Address (InSelf (Field "da")) ]
                  :<:
                    Right 
                      (AddressS
                        ((SelectSelf (Field "a")
                          `Select` Field "ab")
                          `Select` Field "aba")
                        `As` Address (InSelf (Field "daba"))))
                  `Set` GetEnv (Field "y1")
                
              , Address (InSelf (Field "raba"))
                  `Set`
                    (((GetEnv (Field "y1")
                      `Get` Field "a")
                      `Get` Field "ab")
                      `Get` Field "aba")
                      
              ] :<: Nothing)
        in
          do
            run
              (val `Get` Field "raba")
              >>=
              (assertEqual "" $ Number 4)
            
            run
              (val `Get` Field "daba")
              >>=
              (assertEqual "" $ Number 4)
            
    , TestLabel "unpack visible publicly" . TestCase $
        let
          val =
            Structure
              ([ Address (InEnv (Field "w1"))
                  `Set`
                    Structure 
                      ([ Address (InSelf (Field "a"))
                          `Set` NumberLit 1 ]
                      :<: Nothing)
                          
              , Address (InSelf (Field "w2"))
                  `Set`
                    Structure
                      ([ Address (InSelf (Field "b"))
                          `Set` GetSelf (Field "a")
                          
                      , error "unpack" -- T.Unpack (GetEnv (Field "w1")
                      
                      ]
                      :<: Nothing)

              , Address (InSelf (Field "w3"))
                  `Set` (GetSelf (Field "w2") `Get` Field "a")
              
              ] :<: Nothing)
        in
          do
            run 
              ((val
                `Get` Field "w2")
                `Get` Field "b")
              >>=
              (assertEqual "" $ Number 1)
            
            run
              (val `Get` Field "w3")
              >>=
              (assertEqual "" $ Number 1)
            
    , TestLabel "unpack visible privately" . TestCase $
        run
          ((Structure
            ([ Address (InEnv (Field "w1"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
                        
            , Address (InSelf (Field "w2"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "b"))
                        `Set` GetEnv (Field "a")
                        
                    , error "unpack" -- T.Unpack $ GetEnv (Field "w1"
                    
                    ] :<: Nothing)

            ] :<: Nothing)
            `Get` Field "w2")
            `Get` Field "b")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "local private variable unpack visible publicly  ##depreciated behaviour" . TestCase $
        run 
          (Structure
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Structure 
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
                        
            , error "unpack" -- T.Unpack (GetEnv (Field "w1")
             
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
             
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "local private variable unpack visible privately ##depreciated behaviour" . TestCase $
       run
          (Structure
            ([ Address (InEnv (Field "w1"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
            
            , error "unpack" -- T.Unpack (GetEnv (Field "w1")
            
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
            
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" $ Number 1)
          
    , TestLabel "local public variable unpack visible publicly ##depreciated behaviour" . TestCase $
        run 
          (Structure
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
                        
            , error "unpack" -- T.Unpack (GetSelf (Field "w1")
             
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
             
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" (Number 1))
          
    , TestLabel "access member of object with local public variable unpack ##depreciated behaviour" . TestCase $
        run 
          (Structure
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set` IntegerLit 1 ]
                    :<: Nothing)
                        
            , error "unpack" -- T.Unpack (GetSelf (Field "w1")
             
            , Address (InSelf (Field "b"))
                `Set` IntegerLit 2
                
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" (Number 2))
          
    , TestLabel "local public variable unpack visible privately ##depreciated behaviour" . TestCase $
       run
          (Structure
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
            
            , error "unpack" -- T.Unpack (GetSelf (Field "w1")
           
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
           
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" (Number 1))
            
    , TestLabel "parent scope binding" . TestCase $
        run
          ((Structure
            ([ Address (InSelf (Field "inner"))
                `Set` IntegerLit 1
                
            , Address (InEnv (Field "parInner"))
                `Set` GetSelf (Field "inner")
                  
            , Address (InSelf (Field "outer"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "inner"))
                        `Set` IntegerLit 2
                        
                    , Address (InSelf (Field "a"))
                        `Set` GetEnv (Field "parInner")
                        
                    ] :<: Nothing)
                    
            ] :<: Nothing)
            `Get` Field "outer")
            `Get` Field "a")
          >>=
          (assertEqual "" (Number 1))
          
    , TestLabel "unpack scope binding" . TestCase $
        run
          (Structure
            ([ Address (InEnv (Field "inner"))
                `Set`
                  Structure
                    ([ Address (InEnv (Field "var"))
                        `Set` IntegerLit 1
                    
                    , Address (InSelf (Field "innerVar"))
                        `Set` GetEnv (Field "var")
                    
                    ] :<: Nothing)
                    
            , Address (InEnv (Field "outer"))
                `Set`
                  Structure
                    ([ Address (InEnv (Field "var"))
                        `Set` IntegerLit 2
                    
                    , error $ "unpack" -- T.Unpack (GetEnv (Field "inner")
                    
                    ] :<: Nothing)
                    
            , Address (InSelf (Field "a"))
                `Set`
                  (GetEnv (Field "outer")
                    `Get` Field "innerVar")
                    
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" (Number 1))
          
    , TestLabel "self referencing definition" . TestCase $
        run
          (Structure
            ([ Address (InEnv (Field "y"))
                `Set`
                  Structure
                    ([ Address (InSelf (Field "a"))
                        `Set`
                          (GetEnv (Field "y")
                            `Get` Field "b")
                    
                    , Address (InSelf (Field "b"))
                        `Set` NumberLit 1
                    
                    ] :<: Nothing)
                    
            , Address (InSelf (Field "z"))
                `Set`
                  (GetEnv (Field "y") `Get` Field "a")
            
            ] :<: Nothing)
            `Get` Field "z")
          >>=
          (assertEqual "" (Number 1))
          
    , TestLabel "application to referenced outer scope" . TestCase $
        run
          (Structure
            ([ Address (InEnv (Field "y"))
                `Set`
                  Structure 
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1
                    
                    , Address (InEnv (Field "b"))
                        `Set` NumberLit 2
                    
                    , Address (InSelf (Field "x"))
                        `Set`
                          Structure
                            ([ Address (InSelf (Field "a"))
                                `Set` GetEnv (Field "b") ]
                            :<: Nothing)
                                
                    ] :<: Nothing)
                    
            , Address (InSelf (Field "a"))
                `Set`
                  ((GetEnv (Field "y")
                    `Apply`
                      (GetEnv (Field "y") `Get` Field "x"))
                    `Get` Field "a")
                    
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" (Number 2))
          
    , TestLabel "application to nested object" . TestCase $
        let
          r =
            Structure
              ([ Address (InEnv (Field "y"))
                  `Set`
                    Structure
                      ([ Address (InSelf (Field "a"))
                          `Set` NumberLit 1
                          
                      , Address (InSelf (Field "x"))
                          `Set`
                            Structure
                              ([ Address (InSelf (Field "a"))
                                  `Set` NumberLit 2
                                  
                              , Declare (InSelf (Field "x"))
                              
                              ] :<: Nothing)
                              
                      ] :<: Nothing)
                      
              , Address (InSelf (Field "a"))
                  `Set`
                    (((GetEnv (Field "y")
                      `Get` Field "x")
                      `Apply` GetEnv (Field "y"))
                      `Get` Field "a")
              ] :<: Nothing)
              `Get` Field "a"
        in
          run r
          >>=
          (assertEqual (banner r) (Number 1))
          
      , TestLabel "run statement" . TestCase $
          run
            ((Structure $
              [ Address (InEnv (Field "a"))
                  `Set` NumberLit 1
              
              , Run (GetEnv (Field "a"))
              
              , Address (InSelf (Field "b"))
                  `Set` GetEnv (Field "a")
              
              ] :<: Nothing)
              `Get` Field "b")
            >>=
            (assertEqual "" (Number 1))
            
    , TestLabel "run unbound variable" . TestCase $
        catch
          (run
            ((Structure $
              [ Address (InEnv (Field "a"))
                  `Set` NumberLit 1
              
              , Run (GetEnv (Field "x"))
              
              , Address (InSelf (Field "b"))
                  `Set` GetEnv (Field "a")
              
              ]
              :<: Nothing)
              `Get` Field "b")
              >>= assertFailure . show)
          (assertEqual "Unbound var: x" "x" . field)
    ]