{-# LANGUAGE OverloadedStrings #-}
module Test.Core
  ( tests
  )
  where

import qualified Core
import qualified Types.Core as Core
import Types.Classes
import Types.Parser.Short
--import qualified Types.Error as E

import Data.Function( (&) )
import Data.List( elemIndex )
import qualified Data.Map as M
import Control.Monad.Trans
import Test.HUnit
import Bound
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","

parses :: Expr (Vis Tag) -> IO (Core.Expr (Vis Tag))
parses =
  maybe
    (ioError (userError "expr"))
    return
    . Core.getresult . Core.expr
  
  
fails :: Expr (Vis Tag) -> Assertion
fails =
  maybe
    (return ())
    (ioError . userError . showMy)
    . Core.getresult . Core.expr

    
type E = Core.Expr (Vis Tag)


tests =
  test
    [ "number"  ~: do
        r <- parses 1
        let e = Core.Number 1
        assertEqual (banner r) e r
           
    , "string" ~: do
        r <- parses "test"
        let e = Core.String "test"
        assertEqual (banner r) e r
        
    , "public variable" ~: do
        r <- parses (self "public")
        let e = Core.Var (Pub "public")
        assertEqual (banner r) e r
        
    , "private variable" ~: do
        r <- parses (env "private")
        let e = Core.Var (Priv "private")
        assertEqual (banner r) e r
        
    , "field access" ~: do
        r <- parses (env "var" #. "field")
        let e = Core.Var (Priv "var") `Core.At` "field"
        assertEqual (banner r) e r
        
    , "block" ~: 
        [ "public field" ~: do
          r <- (parses . Block) [ self "public" #= 1 ]
          let
            e = (Core.Block [] . M.fromList) [
              ("public", (Scope . Scope . Scope) (Core.Number 1))
              ]
          assertEqual (banner r) e r
       
        , "private field" ~: do
            r <- (parses . Block) [ env "private" #= 1 ]
            let e = Core.Block [(Scope . Scope) (Core.Number 1)] M.empty
            assertEqual (banner r) e r
          
        , "backwards reference" ~: do
            r <- (parses . Block) [ env "one" #= 1, self "oneRef" #= env "one" ]
            let
              e = (Core.Block [(Scope . Scope) (Core.Number 1)] . M.fromList) [
                ("oneRef", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r

        , "forwards reference" ~: do
            r <- (parses . Block) [ self "twoRef" #= env "two", env "two" #= 2 ]
            let
              e = (Core.Block [(Scope . Scope) (Core.Number 2)]. M.fromList) [
                ("twoRef", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r
            
        , "infinite reference" ~: do
            r <- (parses . Block) [ env "selfRef" #= env "selfRef" ]
            let e = Core.Block [(Scope . lift . Core.Var) (B 0)] M.empty
            assertEqual (banner r) e r
            
        , "reference to infinte loop" ~: do
            r <- (parses . Block) [
              env "selfRef" #= env "selfRef",
              self "loop" #= env "selfRef"
              ]
            let
              e = (Core.Block [(Scope . lift . Core.Var) (B 0)] . M.fromList) [
                ("loop", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r
            
        , "private referencing public" ~: do
            r <- (parses . Block) [ self "public" #= 1, env "notPublic" #= self "public" ]
            let
              e = (Core.Block [(lift . Scope . Core.Var) (B "public")]. M.fromList) [
                ("public", (Scope . Scope . Scope) (Core.Number 1))
                ]
            assertEqual (banner r) e r
          
        , "public referenced as private" ~: do
            r <- (parses . Block) [
              self "public" #= 1,
              self "publicAgain" #= env "public"
              ]
            let
              e = (Core.Block []. M.fromList) [
                ("public", (Scope . Scope . Scope) (Core.Number 1)),
                ("publicAgain", (Scope . Scope . Scope . Core.Var) (B "public"))
                ]
            assertEqual (banner r) e r
            
        , "nested scope" ~: do
            r <- (parses . Block) [
              env "outer" #= 1,
              self "object" #= Block [ self "refOuter" #= env "outer" ]
              ]
            let
              e = (Core.Block [(Scope . Scope) (Core.Number 1)] . M.fromList) [
                ("object", (Scope . lift . lift . Core.Block [] . M.fromList) [
                  ("refOuter", (lift . lift . lift . Core.Var) (B 0))
                  ])
                ]
            assertEqual (banner r) e r
          
        , "unbound variable" ~: do
            r <- (parses . Block) [
              self "here" #= 2,
              self "refMissing" #= env "missing"
              ]
            let
              e = (Core.Block [] . M.fromList) [
                ("here", (Scope . Scope . Scope) (Core.Number 2)),
                ("refMissing", (lift . lift . lift . Core.Var) (Priv "missing"))
                ]
            assertEqual (banner r) e r
          
        , "declared variable" ~: do
            r <- (parses . Block) [
                Declare (self "unset"),
                self "set" #= 1
                ]
            let
              e = (Core.Block [] . M.fromList) [
                ("unset", (lift . lift . Scope . Core.Var) (B "unset")),
                ("set", (Scope . Scope . Scope) (Core.Number 1))
                ]
            assertEqual (banner r) e r
            
        , "reference declared variable" ~: do
            r <- (parses . Block) [
                Declare (env "a"),
                self "b" #= env "a"
                ]
            let
              e = (Core.Block [(Scope . lift . Core.Var) (B 0)] . M.fromList) [
                ("b", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r
            
        , "path" ~: do
            r <- (parses . Block) [
              self "a" #. "field" #= 1
              ]
            let
              e = (Core.Block [] . M.fromList) [
                ("a", (Scope . Scope . lift)
                  ((Core.Concat . Core.Block [] . M.fromList) [
                    ("field", (Scope . Scope . Scope) (Core.Number 1))
                    ]
                    (Core.Var (B ()) `Core.Del` "field")))
                ]
            assertEqual (banner r) e r
            
        ]
              
        {-
        , "shadow private variable" ~: do
            r <- (parses . Block) [
                  env "c" #= 1,
                  self "b" #= Block [
                    env "c" #= 2,
                    self "a" #= env "c"
                    ]
                  ]
            let
              e = (Core.Block . M.fromList) [
                ("b", (Scope . Core.Block . M.fromList) [
                  ("a", Scope (Core.Number 2))
                  ])
                ]
            assertEqual (banner r) e r
          
        , "shadow public variable" ~: do
            r <- (parses . Block) [ 
              env "c" #= "hello",
              self "b" #= Block [
                self "field" #= env "c",
                env "c" #= "bye"
                ] #. "field"
              ]
            let
              e = (Core.Block . M.fromList) [
                ("b", Scope (Core.Block (M.fromList [
                  ("field", Scope (Core.String "bye"))
                  ]) `Core.At` "field"))
                ]
            assertEqual (banner r) e r
            
        , "shadowing update using path" ~: do
            r <- (parses . Block) [
              env "c0" #= Block [
                self "f" #= 1,
                self "g" #= env "x"
                ],
              self "d" #= Block [
                env "c" #. "g" #= env "y",
                self "h" #= env "c"
                ]
              ]
            let
              e = (Core.Block . M.fromList) [
                ("d", (Scope . Core.Block . M.fromList) [
                  ("h", (Scope . Core.Block . M.fromList) [
                    ("f", Scope (Core.Number 1)),
                    ("g", (Scope . Core.Var . F . Core.Var . F . Core.Var . F . Core.Var) (Priv "y"))
                    ])
                  ])
                ]
            assertEqual (banner r) e r
            
        ]
        
    , "update" ~: do
        r <- parses (Block [
          self "a" #= 2,
          self "b" #= env "a"
          ] `Update` env "y")
        let
          e = (Core.Block . M.fromList) [
            ("a", Scope (Core.Number 2)), 
            ("b", (Scope . Core.Var . F . Core.Var) (Priv "a"))
            ] `Core.Update` Core.Var (Priv "y")
        assertEqual (banner r) e r
      
    {--}
    , TestLabel "shadowing update" . TestCase $
        run
          ((Block
            ([ Address (InEnv (Field "outer"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
            
            , Address (InSelf (Field "inner"))
                `Set`
                  Block
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
          (assertEqual "" $ Core.Number 3)
          
    , TestLabel "shadowing update 2" . TestCase $
        run
          (Block
            ([ Address (InEnv (Field "outer"))
                `Set`
                  Block 
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 2
                    
                    , Address (InSelf (Field "b"))
                        `Set` NumberLit 1
                    
                    ] :<: Nothing)
                    
            , Address (InSelf (Field "inner"))
                `Set`
                  Block
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
          (assertEqual "" $ Core.Number 3)
          
    , TestLabel "destructuring" . TestCase $
        let
          val = 
            Block
              ([ Address (InEnv (Field "obj"))
                  `Set`
                    Block
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
              (assertEqual "" $ Core.Number 2)
            
            run (val `Get` Field "db")
              >>=
              (assertEqual "" $ Core.Number 3)
            
    , TestLabel "destructuring unpack" . TestCase $
        run
          (Block
            ([ Address (InEnv (Field "obj"))
                `Set`
                  Block
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
          (assertEqual "" $ Core.Number 3)
          
    , TestLabel "nested destructuring" . TestCase $
        let 
          val =
            Block
              ([ Address (InEnv (Field "y1"))
                  `Set`
                    Block
                      ([ Address (InSelf (Field "a"))
                          `Set`
                            Block
                              ([ Address (InSelf (Field "aa"))
                                  `Set` NumberLit 3
                              
                              , Address (InSelf (Field "ab"))
                                  `Set`
                                    Block
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
              (assertEqual "" $ Core.Number 4)
            
            run
              (val `Get` Field "daba")
              >>=
              (assertEqual "" $ Core.Number 4)
            
    , TestLabel "unpack visible publicly" . TestCase $
        let
          val =
            Block
              ([ Address (InEnv (Field "w1"))
                  `Set`
                    Block 
                      ([ Address (InSelf (Field "a"))
                          `Set` NumberLit 1 ]
                      :<: Nothing)
                          
              , Address (InSelf (Field "w2"))
                  `Set`
                    Block
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
              (assertEqual "" $ Core.Number 1)
            
            run
              (val `Get` Field "w3")
              >>=
              (assertEqual "" $ Core.Number 1)
            
    , TestLabel "unpack visible privately" . TestCase $
        run
          ((Block
            ([ Address (InEnv (Field "w1"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
                        
            , Address (InSelf (Field "w2"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "b"))
                        `Set` GetEnv (Field "a")
                        
                    , error "unpack" -- T.Unpack $ GetEnv (Field "w1"
                    
                    ] :<: Nothing)

            ] :<: Nothing)
            `Get` Field "w2")
            `Get` Field "b")
          >>=
          (assertEqual "" $ Core.Number 1)
          
    , TestLabel "local private variable unpack visible publicly  ##depreciated behaviour" . TestCase $
        run 
          (Block
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Block 
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
                        
            , error "unpack" -- T.Unpack (GetEnv (Field "w1")
             
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
             
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" $ Core.Number 1)
          
    , TestLabel "local private variable unpack visible privately ##depreciated behaviour" . TestCase $
       run
          (Block
            ([ Address (InEnv (Field "w1"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
            
            , error "unpack" -- T.Unpack (GetEnv (Field "w1")
            
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
            
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" $ Core.Number 1)
          
    , TestLabel "local public variable unpack visible publicly ##depreciated behaviour" . TestCase $
        run 
          (Block
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
                        
            , error "unpack" -- T.Unpack (GetSelf (Field "w1")
             
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
             
            ] :<: Nothing)
            `Get` Field "a")
          >>=
          (assertEqual "" (Core.Number 1))
          
    , TestLabel "access member of object with local public variable unpack ##depreciated behaviour" . TestCase $
        run 
          (Block
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "a"))
                        `Set` IntegerLit 1 ]
                    :<: Nothing)
                        
            , error "unpack" -- T.Unpack (GetSelf (Field "w1")
             
            , Address (InSelf (Field "b"))
                `Set` IntegerLit 2
                
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" (Core.Number 2))
          
    , TestLabel "local public variable unpack visible privately ##depreciated behaviour" . TestCase $
       run
          (Block
            ([ Address (InSelf (Field "w1"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1 ]
                    :<: Nothing)
            
            , error "unpack" -- T.Unpack (GetSelf (Field "w1")
           
            , Address (InSelf (Field "b"))
                `Set` GetEnv (Field "a")
           
            ] :<: Nothing)
            `Get` Field "b")
          >>=
          (assertEqual "" (Core.Number 1))
            
    , TestLabel "parent scope binding" . TestCase $
        run
          ((Block
            ([ Address (InSelf (Field "inner"))
                `Set` IntegerLit 1
                
            , Address (InEnv (Field "parInner"))
                `Set` GetSelf (Field "inner")
                  
            , Address (InSelf (Field "outer"))
                `Set`
                  Block
                    ([ Address (InSelf (Field "inner"))
                        `Set` IntegerLit 2
                        
                    , Address (InSelf (Field "a"))
                        `Set` GetEnv (Field "parInner")
                        
                    ] :<: Nothing)
                    
            ] :<: Nothing)
            `Get` Field "outer")
            `Get` Field "a")
          >>=
          (assertEqual "" (Core.Number 1))
          
    , TestLabel "unpack scope binding" . TestCase $
        run
          (Block
            ([ Address (InEnv (Field "inner"))
                `Set`
                  Block
                    ([ Address (InEnv (Field "var"))
                        `Set` IntegerLit 1
                    
                    , Address (InSelf (Field "innerVar"))
                        `Set` GetEnv (Field "var")
                    
                    ] :<: Nothing)
                    
            , Address (InEnv (Field "outer"))
                `Set`
                  Block
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
          (assertEqual "" (Core.Number 1))
          
    , TestLabel "self referencing definition" . TestCase $
        run
          (Block
            ([ Address (InEnv (Field "y"))
                `Set`
                  Block
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
          (assertEqual "" (Core.Number 1))
          
    , TestLabel "application to referenced outer scope" . TestCase $
        run
          (Block
            ([ Address (InEnv (Field "y"))
                `Set`
                  Block 
                    ([ Address (InSelf (Field "a"))
                        `Set` NumberLit 1
                    
                    , Address (InEnv (Field "b"))
                        `Set` NumberLit 2
                    
                    , Address (InSelf (Field "x"))
                        `Set`
                          Block
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
          (assertEqual "" (Core.Number 2))
          
    , TestLabel "application to nested object" . TestCase $
        let
          r =
            Block
              ([ Address (InEnv (Field "y"))
                  `Set`
                    Block
                      ([ Address (InSelf (Field "a"))
                          `Set` NumberLit 1
                          
                      , Address (InSelf (Field "x"))
                          `Set`
                            Block
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
          (assertEqual (banner r) (Core.Number 1))
          
      , TestLabel "run statement" . TestCase $
          run
            ((Block $
              [ Address (InEnv (Field "a"))
                  `Set` NumberLit 1
              
              , Run (GetEnv (Field "a"))
              
              , Address (InSelf (Field "b"))
                  `Set` GetEnv (Field "a")
              
              ] :<: Nothing)
              `Get` Field "b")
            >>=
            (assertEqual "" (Core.Number 1))
            
    , TestLabel "run unbound variable" . TestCase $
        catch
          (run
            ((Block $
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
    -}
    ]