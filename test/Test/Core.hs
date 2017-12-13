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

import qualified Data.Map as M
import Control.Monad.Trans
import Test.HUnit hiding ( Label )
import Bound
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","

parses :: Syntax -> IO (Core.Expr (Vis Core.Id))
parses =
  maybe
    (ioError (userError "expr"))
    return
    . Core.getresult . Core.expr
  
  
fails :: (e -> Assertion) -> Syntax -> Assertion
fails _ =
  maybe
    (return ())
    (ioError . userError . show)
    . Core.getresult . Core.expr



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
        r <- parses (self' "public")
        let e = (Core.Var . Pub) (Label "public")
        assertEqual (banner r) e r
        
    , "private variable" ~: do
        r <- parses (env' "private")
        let e = Core.Var (Priv "private")
        assertEqual (banner r) e r
        
    , "field access" ~: do
        r <- parses (env' "var" #. "field")
        let e = Core.Var (Priv "var") `Core.At` Label "field"
        assertEqual (banner r) e r
        
    , "block" ~: 
        [ "assign public field" ~: do
          r <- (parses . block') [ self' "public" #= 1 ]
          let
            e = (Core.Block [] . M.fromList) [
              (Label "public", (Scope . Scope . Scope) (Core.Number 1))
              ]
          assertEqual (banner r) e r
       
        , "assign private field" ~: do
            r <- (parses . block') [ env' "private" #= 1 ]
            let e = Core.Block [(Scope . Scope) (Core.Number 1)] M.empty
            assertEqual (banner r) e r
          
        , "backwards reference" ~: do
            r <- (parses . block') [ env' "one" #= 1, self' "oneRef" #= env' "one" ]
            let
              e = (Core.Block [(Scope . Scope) (Core.Number 1)] . M.fromList) [
                (Label "oneRef", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r

        , "forwards reference" ~: do
            r <- (parses . block') [ self' "twoRef" #= env' "two", env' "two" #= 2 ]
            let
              e = (Core.Block [(Scope . Scope) (Core.Number 2)]. M.fromList) [
                (Label "twoRef", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r
            
        , "infinite reference" ~: do
            r <- (parses . block') [ env' "selfRef" #= env' "selfRef" ]
            let e = Core.Block [(Scope . lift . Core.Var) (B 0)] M.empty
            assertEqual (banner r) e r
            
        , "reference to infinte loop" ~: do
            r <- (parses . block') [
              env' "selfRef" #= env' "selfRef",
              self' "loop" #= env' "selfRef"
              ]
            let
              e = (Core.Block [(Scope . lift . Core.Var) (B 0)] . M.fromList) [
                (Label "loop", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r
            
        , "private referencing public" ~: do
            r <- (parses . block') [
              self' "public" #= 1,
              env' "notPublic" #= self' "public"
              ]
            let
              e = (Core.Block [(lift . Scope . Core.Var . B) (Label "public")]. M.fromList) [
                (Label "public", (Scope . Scope . Scope) (Core.Number 1))
                ]
            assertEqual (banner r) e r
          
        , "public referenced as private" ~: do
            r <- (parses . block') [
              self' "public" #= 1,
              self' "publicAgain" #= env' "public"
              ]
            let
              e = (Core.Block []. M.fromList) [
                (Label "public", (Scope . Scope . Scope) (Core.Number 1)),
                (Label "publicAgain", (Scope . Scope . Scope . Core.Var . B) (Label "public"))
                ]
            assertEqual (banner r) e r
            
        , "nested scope" ~: do
            r <- (parses . block') [
              env' "outer" #= 1,
              self' "object" #= block' [ self' "refOuter" #= env' "outer" ]
              ]
            let
              e = (Core.Block [(Scope . Scope) (Core.Number 1)] . M.fromList) [
                (Label "object", (Scope . lift . lift . Core.Block [] . M.fromList) [
                  (Label "refOuter", (lift . lift . lift . Core.Var) (B 0))
                  ])
                ]
            assertEqual (banner r) e r
          
        , "unbound variable" ~: do
            r <- (parses . block') [
              self' "here" #= 2,
              self' "refMissing" #= env' "missing"
              ]
            let
              e = (Core.Block [] . M.fromList) [
                (Label "here", (Scope . Scope . Scope) (Core.Number 2)),
                (Label "refMissing", (lift . lift . lift . Core.Var) (Priv "missing"))
                ]
            assertEqual (banner r) e r
          
        , "declared variable" ~: do
            r <- (parses . block') [
                Declare (self' "unset"),
                self' "set" #= 1
                ]
            let
              e = (Core.Block [] . M.fromList) [
                (Label "unset", (Scope . Scope) (Scope Core.Undef)),
                (Label "set", (Scope . Scope . Scope) (Core.Number 1))
                ]
            assertEqual (banner r) e r
            
        , "reference declared variable" ~: do
            r <- (parses . block') [
                Declare (env' "a"),
                self' "b" #= env' "a"
                ]
            let
              e = (Core.Block [Scope (Scope Core.Undef)] . M.fromList) [
                (Label "b", (Scope . lift . lift . Core.Var) (B 0))
                ]
            assertEqual (banner r) e r
            
        , "assign public path" ~: do
            r <- (parses . block') [ self' "a" #. "field" #= 1 ]
            let
              e = (Core.Block [] . M.fromList) [
                (Label "a", (Scope . Scope . lift)
                  ((Core.Block [] . M.fromList) [
                    (Label "field", (Scope . Scope . Scope) (Core.Number 1))
                    ] `Core.Concat`
                    (Core.Var (B ()) `Core.Fix` Label "field")))
                ]
            assertEqual (banner r) e r
            
        , "public reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= self' "f" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", (toScope . toScope . toScope) ((Core.Block [] . M.fromList) [
                (Label "f", (toScope . toScope . toScope . Core.Var . F . F . F . B) (Label "f"))
                ] `Core.Concat` ((Core.Var . F) (B ()) `Core.Fix` Label "f")))
              ] in
            parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= env' "f" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", (toScope . toScope . toScope) ((Core.Block [] . M.fromList) [
                (Label "f", (toScope . toScope . toScope . Core.Var . F . F . F . F . F . F) (Priv "f"))
                ] `Core.Concat` ((Core.Var . F) (B ()) `Core.Fix` Label "f")))
              ] in
            parses r >>= assertEqual (banner r) e
              
            
        , "assign private path" ~: let
            r = block' [ env' "var" #. "field" #= 2 ]
            e = Core.Block [
              (lift . lift) ((Core.Block [] . M.fromList) [
                (Label "field", (Scope . Scope . Scope) (Core.Number 2))
                ] `Core.Concat`
                (Core.Var (Priv "var") `Core.Fix` Label "field"))
              ] M.empty in
            parses r >>= assertEqual (banner r) e
            
        , "shadow private variable" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "inner" #= block' [
                env' "outer" #= 2,
                self' "shadow" #= env' "outer"
                ]
              ]
            e = (Core.Block [(Scope . Scope) (Core.Number 1)] . M.fromList) [
              (Label "inner", (lift . Scope . Scope . Core.Block [
                (Scope . Scope) (Core.Number 2)
                ] . M.fromList) [
                (Label "shadow", (Scope . lift . lift . Core.Var) (B 0))
                ])
              ] in
            parses r >>= assertEqual (banner r) e
          
        , "shadow public variable" ~: do
            r <- (parses . block') [ 
              self' "outer" #= "hello",
              self' "inner" #= block' [
                self' "shadow" #= env' "outer",
                env' "outer" #= "bye"
                ] #. "shadow"
              ]
            let
              e = (Core.Block [] . M.fromList) [
                (Label "outer", (Scope . Scope . Scope) (Core.String "hello")),
                (Label "inner", (Scope . Scope . Scope) (((Core.Block [
                  (Scope . Scope) (Core.String "bye")
                  ] . M.fromList) [
                  (Label "shadow", (Scope . lift . lift . Core.Var) (B 0))
                  ]) `Core.At` Label "shadow"))
                ]
            assertEqual (banner r) e r
            
        , "shadowing update public using path" ~: let
            r = block' [
              self' "inner" #= block' [
                self' "var" #. "g" #= env' "y"
                ]
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "inner", (lift . lift . lift . Core.Block [] . M.fromList) [
                (Label "var", (lift . Scope . lift) ((Core.Var . F . lift . Core.Block [] . M.fromList) [
                  (Label "g", (lift . lift . lift . Core.Var) (Priv "y"))
                  ] `Core.Concat` (Core.Var (B ()) `Core.Fix` Label "g")))
                ])
              ] in
            parses r >>= assertEqual (banner r) e
            
        , "shadowing private using path" ~: let
            r = block' [
              env' "outer" #= block' [ self' "g" #= "hello" ],
              self' "inner" #= block' [ env' "outer" #. "g" #= "bye" ]
              ]
            e = (Core.Block [
              (Scope . Scope . Core.Block [] . M.fromList) [
                (Label "g", (Scope . Scope . Scope) (Core.String "hello"))
                ]
              ] . M.fromList) [
                (Label "inner", (Scope . lift . lift) (Core.Block [
                  (lift . lift) ((Core.Block [] . M.fromList) [
                    (Label "g", (Scope . Scope . Scope) (Core.String "bye"))
                    ] `Core.Concat` (Core.Var (B 0) `Core.Fix` Label "g"))
                  ] M.empty))
                ] in
            parses r >>= assertEqual (banner r) e
            
        ]
    
    , "update" ~: do
        r <- parses (block' [
          self' "a" #= 2,
          self' "b" #= env' "a"
          ] # env' "y")
        let
          e = (Core.Block [] . M.fromList) [
            (Label "a", (Scope . Scope . Scope) (Core.Number 2)), 
            (Label "b", (Scope . Scope . Scope . Core.Var. B) (Label "a"))
            ] `Core.Update` Core.Var (Priv "y")
        assertEqual (banner r) e r
      
    , "destructuring" ~: do
        r <- (parses . block') [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock' [
            self' "a" #= self' "da",
            self' "b" #= self' "db"
            ] #= env' "obj"
          ]
        let 
          e = (Core.Block [
            (Scope . Scope . Core.Block [] . M.fromList) [
              (Label "a", (Scope . Scope . Scope) (Core.Number 2)),
              (Label "b", (Scope . Scope . Scope) (Core.Number 3))
              ]
            ] . M.fromList) [
              (Label "da", (Scope . lift . lift) (Core.Var (B 0) `Core.At` Label "a")),
              (Label "db", (Scope . lift . lift) (Core.Var (B 0) `Core.At` Label "b"))
              ]
        assertEqual (banner r) e r
        
    , "destructuring unpack" ~: do
        r <- parses (block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock'' [ self' "a" #= self' "da" ] (self' "db") #= env' "obj"
          ] #. "b")
        let
          e = (Core.Block [
            (Scope . Scope . Core.Block [] . M.fromList) [
              (Label "a", (Scope . Scope . Scope) (Core.Number 2)),
              (Label "b", (Scope . Scope . Scope) (Core.Number 3))
              ]
            ] . M.fromList) [
              (Label "da", (Scope . lift . lift) (Core.Var (B 0) `Core.At` Label "a")),
              (Label "b", (Scope . lift . lift) (Core.Var (B 0) `Core.Fix` Label "a"))
            ] `Core.At` Label "b"
        assertEqual (banner r) e r
        
    , "nested destructuring" ~: do
        r <- (parses . block') [
          env' "y1" #= block' [
            self' "a" #= block' [
              self' "aa" #= 3,
              self' "ab" #= block' [ self' "aba" #= 4 ]
              ]
            ],
          setblock' [
            self' "a" #. "aa" #= self' "da",
            self' "a" #. "ab" #. "aba" #= self' "daba"
            ] #= env' "y1", 
          self' "raba" #=  env' "y1" #. "a" #. "ab" #. "aba"
          ]
        let
          e = (Core.Block [
            (Scope . Scope . Core.Block [] . M.fromList) [
              (Label "a", (Scope . Scope . Scope . Core.Block [] . M.fromList) [
                (Label "aa", (Scope . Scope . Scope) (Core.Number 3)),
                (Label "ab", (Scope . Scope . Scope . Core.Block [] . M.fromList) [
                  (Label "aba", (Scope . Scope . Scope) (Core.Number 4))
                  ])
                ])
              ]
            ] . M.fromList) [
              (Label "da", (Scope . lift . lift) ((Core.Var (B 0) `Core.At` Label "a") `Core.At` Label "aa")),
              (Label "daba", (Scope . lift . lift) (((Core.Var (B 0) `Core.At` Label "a") `Core.At` Label "ab") `Core.At` Label "aba")),
              (Label "raba", (Scope . lift . lift) (((Core.Var (B 0) `Core.At` Label "a") `Core.At` Label "ab") `Core.At` Label "aba"))
              ]
        assertEqual (banner r) e r
    
    , "parent scope binding" ~: do
        r <- (parses . block') [
          self' "inner" #= 1,
          env' "parInner" #= self' "inner",
          self' "outer" #= block' [
            self' "inner" #= 2,
            self' "a" #= env' "parInner"
            ]
          ]
        let
          e = (Core.Block [(Scope . Scope . Core.Var . B) (Label "inner")] . M.fromList) [
            (Label "inner", (Scope . Scope . Scope) (Core.Number 1)),
            (Label "outer", (Scope . lift . lift . Core.Block [] . M.fromList) [
              (Label "inner", (Scope . Scope . Scope) (Core.Number 2)),
              (Label "a", (lift . lift . lift . Core.Var) (B 0))
              ])
            ]
        assertEqual (banner r) e r
      
    , "self referencing definition" ~: do
        r <- (parses . block') [
          env' "y" #= block' [
            self' "a" #= env' "y" #. "b",
            self' "b" #= 1
            ],
          self' "z" #= env' "y" #. "a"
          ]
        let
          e = (Core.Block [
            (Scope . lift . Core.Block [] . M.fromList) [
              (Label "a", (lift . lift . lift) (Core.Var (B 0) `Core.At` Label "b")),
              (Label "b", (Scope . Scope . Scope) (Core.Number 1))
              ]
            ] . M.fromList) [
              (Label "z", (Scope . lift . lift) (Core.Var (B 0) `Core.At` Label "a"))
              ]
        assertEqual (banner r) e r
          
    , "application to referenced outer scope" ~: do
        r <- (parses . block') [
          env' "y" #= block' [
            self' "a" #= 1,
            env' "b" #= 2,
            self' "x" #= block' [ self' "a" #= env' "b" ]
            ],
          self' "a" #= env' "y" # (env' "y" #. "x") #. "a"
          ]
        let
          e = (Core.Block [
            (Scope . Scope . Core.Block [(Scope . Scope) (Core.Number 2)] . M.fromList) [
              (Label "a", (Scope . Scope . Scope) (Core.Number 1)),
              (Label "x", (Scope . lift . lift . Core.Block [] . M.fromList) [
                (Label "a", (lift . lift . lift . Core.Var) (B 0))
                ])
              ]
            ] . M.fromList) [
              (Label "a", (Scope . lift . lift) ((Core.Var (B 0) `Core.Update` (Core.Var (B 0) `Core.At` Label "x")) `Core.At` Label "a"))
            ]
        assertEqual (banner r) e r
        
    , "application to nested object" ~: do
        r <- (parses . block') [
          env' "y" #= block' [
            self' "a" #= 1,
            self' "x" #= block' [
              self' "a" #= 2,
              Declare (self' "x")
              ]
            ],
          self' "a" #= env' "y" #. "x" # (env' "y" #. "a")
          ]
        let
          e = (Core.Block [
            (Scope . Scope . Core.Block [] . M.fromList) [
              (Label "a", (Scope . Scope . Scope) (Core.Number 1)),
              (Label "x", (Scope . Scope . Scope . Core.Block [] . M.fromList) [
                (Label "a", (Scope . Scope . Scope) (Core.Number 2)),
                (Label "x", (Scope . Scope) (Scope Core.Undef))
                ])
              ]
            ] . M.fromList) [
              (Label "a", (Scope . lift . lift) ((Core.Var (B 0) `Core.At` Label "x") `Core.Update` (Core.Var (B 0) `Core.At` Label "a")))
            ]
        assertEqual (banner r) e r
        
    ]