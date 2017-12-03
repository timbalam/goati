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
                  ((Core.Block [] . M.fromList) [
                    ("field", (Scope . Scope . Scope) (Core.Number 1))
                    ] `Core.Concat`
                    (Core.Var (B ()) `Core.Del` "field")))
                ]
            assertEqual (banner r) e r
            
        , "shadow private variable" ~: do
            r <- (parses . Block) [
              env "outer" #= 1,
              self "inner" #= Block [
                env "outer" #= 2,
                self "shadow" #= env "outer"
                ]
              ]
            let
              e = (Core.Block [(Scope . Scope) (Core.Number 1)] . M.fromList) [
                ("inner", (lift . Scope . Scope . Core.Block [
                  (Scope . Scope) (Core.Number 2)
                  ] . M.fromList) [
                  ("shadow", (Scope . lift . lift . Core.Var) (B 0))
                  ])
                ]
            assertEqual (banner r) e r
          
        , "shadow public variable" ~: do
            r <- (parses . Block) [ 
              self "outer" #= "hello",
              self "inner" #= Block [
                self "shadow" #= env "outer",
                env "outer" #= "bye"
                ] #. "shadow"
              ]
            let
              e = (Core.Block [] . M.fromList) [
                ("outer", (Scope . Scope . Scope) (Core.String "hello")),
                ("inner", (Scope . Scope . Scope) (((Core.Block [
                  (Scope . Scope) (Core.String "bye")
                  ] . M.fromList) [
                  ("shadow", (Scope . lift . lift . Core.Var) (B 0))
                  ]) `Core.At` "shadow"))
                ]
            assertEqual (banner r) e r
            
        , "shadowing update using path" ~: do
            r <- (parses . Block) [
              self "inner" #= Block [
                self "var" #. "g" #= env "y"
                ]
              ]
            let
              e = (Core.Block [] . M.fromList) [
                ("inner", (lift . lift . lift . Core.Block [] . M.fromList) [
                  ("var", (lift . Scope . lift) ((Core.Var . F . lift . Core.Block [] . M.fromList) [
                    ("g", (lift . lift . lift . Core.Var) (Priv "y"))
                    ] `Core.Concat` (Core.Var (B ()) `Core.Del` "g")))
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
          e = (Core.Block [] . M.fromList) [
            ("a", (Scope . Scope . Scope) (Core.Number 2)), 
            ("b", (lift . lift . lift . Core.Var) (Priv "a"))
            ] `Core.Update` Core.Var (Priv "y")
        assertEqual (banner r) e r
      
    , TestLabel "destructuring" . TestCase $ do
        r <- (parses . Block) [
          env "obj" #= Block [
            self "a" #= 2,
            self "b" #= 3
            ],
          SetBlock [
            self "a" #= self "da",
            self "b" #= self "db"
            ] #= env "obj"
          ]
        let 
          e = (Core.Block [
            (Scope . Scope . Core.Block [] . M.fromList) [
              ("a", (Scope . Scope . Scope) (Core.Number 2)),
              ("b", (Scope . Scope . Scope) (Core.Number 3))
              ]
            ] . M.fromList) [
              ("da", (Scope . lift . lift) (Core.Var (B 0) `Core.At` "a")),
              ("db", (Scope . lift . lift) (Core.Var (B 0) `Core.At` "b"))
              ]
        assertEqual (banner r) e r
        
    , TestLabel "destructuring unpack" . TestCase $ do
        r <- parses (Block [
          env "obj" #= Block [
            self "a" #= 2,
            self "b" #= 3
            ],
          SetBlock [ self "a" #= self "da" ] #= env "obj"
          ] #. "b")
        let
          e = (Core.Block [
            (Scope . Scope . Core.Block [] . M.fromList) [
              ("a", (Scope . Scope . Scope) (Core.Number 2)),
              ("b", (Scope . Scope . Scope) (Core.Number 3))
              ]
            ] . M.fromList) [
              ("da", (Scope . lift . lift) (Core.Var (B 0) `Core.At` "a")
            ] `Core.At` "b"
        assertEqual (banner r) e r
        
    , TestLabel "nested destructuring" . TestCase $ do
        r <- (parses . Block) [
          env "y1" #= Block [
            self "a" #= Block [
              self "aa" #= 3,
              self "ab" #= Block [ self "aba" #= 4 ]
            ],
          SetBlock [
            self "a" #. "aa" #= self "da",
            self "a" #. "ab" #. "aba" #= self "daba"
            ] #= env "y1", 
          self "raba" #=  env "y1" #. "a" #. "ab" #. "aba"
          ]
        let
          e = (Core.Block [
            (Scope . Scope . Core.Block [] . M.fromList) [
              ("a", (Scope . Scope . Scope . Core.Block [] . M.fromList) [
                ("aa", (Scope . Scope . Scope) (Core.Number 3)),
                ("ab", (Scope . Scope . Scope . Core.Block [] . M.fromList) [
                  ("aba", (Scope . Scope . Scope) (Core.Number 4))
                  ])
              ])
            ] . M.fromList) [
              ("da", (Scope . lift . lift) ((Core.Var (B 0) `Core.At` "a") `Core.At` "aa")),
              ("daba", (Scope . lift . lift) (((Core.Var (B 0) `Core.At` "a") `Core.At` "ab") `Core.At` "aba"),
              ("raba", (Scope . lift . lift) (((Core.Var (B 0) `Core.At` "a") `Core.At` "ab") `Core.At` "aba"))
              ]
        assertEqual (banner r) e r
    
    , TestLabel "parent scope binding" . TestCase $ do
        r <- (parses . Block) [
          self "inner" #= 1,
          env "parInner" #= self "inner",
          self "outer" #= Block [
            self "inner" #= 2,
            self "a" #= env "parInner"
            ]
          ]
        let
          e = (Core.Block [(lift . Scope . Core.Var) (B "inner")] . M.fromList) [
            ("inner", (Scope . Scope . Scope) (Core.Number "1")),
            ("outer", (lift . lift . lift . Core.Block [] . M.fromList) [
              ("inner", (Scope . Scope . Scope) (Core.Number 1)),
              ("a", (lift . lift . lift . Core.Var) (B 0))
              ])
            ]
            
        assertEqual (banner r) e r
        
    {-
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