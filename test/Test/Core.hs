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
import Bound --( toScope, Var(..) )
  
  
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
    
    
enscopeExpr = Core.Enscope . toScope . toScope . Core.liftExpr
enscopeEval = Core.Enscope . toScope . toScope
enF = F . F
    

tests =
  test
    [ "number"  ~: let
        r = 1
        e = Core.Number 1
        in
        parses r >>= assertEqual (banner r) e
           
    , "string" ~: let
        r = "test"
        e = Core.String "test"
        in
        parses r >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r = self' "public"
        e = (Core.Var . Pub) (Label "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env' "private"
        e = Core.Var (Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env' "var" #. "field"
        e = Core.Var (Priv "var") `Core.At` Label "field"
        in
        parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "assign public field" ~: let 
          r = block' [ self' "public" #= 1 ]
          e = (Core.Block [] . M.fromList) [
            (Label "public", enscopeExpr (Core.Number 1))
            ]
          in
          parses r >>= assertEqual (banner r) e
       
        , "assign private field" ~: let
            r = block' [ env' "private" #= 1 ]
            e = Core.Block [enscopeExpr (Core.Number 1)] M.empty
            in
            parses r >>= assertEqual (banner r) e
          
        , "backwards reference" ~: let
            r = block' [ env' "one" #= 1, self' "oneRef" #= env' "one" ]
            e = (Core.Block [enscopeExpr (Core.Number 1)]
              . M.fromList) [
              (Label "oneRef", (enscopeExpr . Core.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "forwards reference" ~: let
            r = block' [ self' "twoRef" #= env' "two", env' "two" #= 2 ]
            e = (Core.Block [enscopeExpr (Core.Number 2)]
              . M.fromList) [
              (Label "twoRef", (enscopeExpr . Core.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = block' [ env' "selfRef" #= env' "selfRef" ]
            e = Core.Block [(enscopeExpr . Core.Var . F) (B 0)] M.empty
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = block' [
              env' "selfRef" #= env' "selfRef",
              self' "loop" #= env' "selfRef"
              ]
            e = (Core.Block [(enscopeExpr . Core.Var . F) (B 0)] . M.fromList) [
              (Label "loop",
                (enscopeExpr . Core.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "private referencing public" ~: let
            r = block' [
              self' "public" #= 1,
              env' "notPublic" #= self' "public"
              ]
            e = (Core.Block [
              (enscopeExpr . Core.Var . B) (Label "public")
              ]. M.fromList) [
              (Label "public", enscopeExpr (Core.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "public referenced as private" ~: let
            r = block' [
              self' "public" #= 1,
              self' "publicAgain" #= env' "public"
              ]
            e = (Core.Block []. M.fromList) [
              (Label "public", enscopeExpr (Core.Number 1)),
              (Label "publicAgain",
                (enscopeExpr . Core.Var . B) (Label "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "object" #= block' [ self' "refOuter" #= env' "outer" ]
              ]
            e = (Core.Block [enscopeExpr (Core.Number 1)]
              . M.fromList) [
              (Label "object",
                (enscopeExpr . Core.Block [] . M.fromList) [
                  (Label "refOuter",
                    (enscopeExpr . Core.Var . enF . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "unbound variable" ~: let
            r = block' [
              self' "here" #= 2,
              self' "refMissing" #= env' "missing"
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "here", enscopeExpr (Core.Number 2)),
              (Label "refMissing",
                (enscopeExpr . Core.Var . enF) (Priv "missing"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "declared variable" ~: let
            r = block' [
              Declare (self' "unset"),
              self' "set" #= 1
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "unset", enscopeEval (Core.Eval Nothing)),
              (Label "set", enscopeExpr (Core.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference declared variable" ~: let
            r = block' [
              Declare (env' "a"),
              self' "b" #= env' "a"
              ]
            e = (Core.Block [enscopeEval (Core.Eval Nothing)] . M.fromList) [
              (Label "b",
                (enscopeExpr . Core.Var . F) (B 0))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign public path" ~: let
            r = block' [ self' "a" #. "field" #= 1 ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", enscopeExpr
                ((Core.Block [] . M.fromList) [
                  (Label "field", enscopeExpr (Core.Number 1))
                  ] `Core.Concat` Core.Eval Nothing))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= self' "f" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", enscopeExpr
                ((Core.Block [] . M.fromList) [
                (Label "f",
                  (enscopeExpr . Core.Var . enF . B) (Label "f"))
                ] `Core.Concat` Core.Eval Nothing))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign expression with public references to long path" ~: let
            r = block' [ self' "a" #. "f" #. "g" #= self' "f" # self' "g" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", enscopeExpr ((Core.Block [] . M.fromList) [
                (Label "f", enscopeExpr ((Core.Block [] . M.fromList) [
                  (Label "g", enscopeExpr
                    ((Core.Var . enF . enF . B) (Label "f") `Core.Update`
                      (Core.Var . enF . enF . B) (Label "g")))
                  ] `Core.Concat` Core.Eval Nothing))
                ] `Core.Concat` Core.Eval Nothing))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= env' "f" ]
            e = (Core.Block [] . M.fromList) [
              (Label "a", enscopeExpr ((Core.Block [] . M.fromList) [
                (Label "f",
                  (enscopeExpr . Core.Var . enF . enF) (Priv "f"))
                ] `Core.Concat` Core.Eval Nothing))
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = block' [ env' "var" #. "field" #= 2 ]
            e = Core.Block [
              enscopeExpr ((Core.Block [] . M.fromList) [
                (Label "field",
                  enscopeExpr (Core.Number 2))
                ] `Core.Concat` Core.liftExpr
                ((Core.Var . enF) (Priv "var") `Core.Fix`
                  Label "field"))
              ] M.empty
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadow private variable" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "inner" #= block' [
                env' "outer" #= 2,
                self' "shadow" #= env' "outer"
                ]
              ]
            e = (Core.Block [enscopeExpr (Core.Number 1)]
              . M.fromList) [
              (Label "inner", (enscopeExpr . Core.Block [
                enscopeExpr (Core.Number 2)
                ] . M.fromList) [
                (Label "shadow", (enscopeExpr . Core.Var . F) (B 0))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "shadow public variable" ~: let
            r = block' [ 
              self' "outer" #= "hello",
              self' "inner" #= block' [
                self' "shadow" #= env' "outer",
                env' "outer" #= "bye"
                ] #. "shadow"
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "outer",
                enscopeExpr (Core.String "hello")),
              (Label "inner", enscopeExpr (((Core.Block [
                enscopeExpr (Core.String "bye")
                ] . M.fromList) [
                (Label "shadow",
                  (enscopeExpr . Core.Var . F) (B 0))
                ]) `Core.At` Label "shadow"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "shadowing update public using path" ~: let
            r = block' [
              self' "inner" #= block' [
                self' "var" #. "g" #= env' "y"
                ]
              ]
            e = (Core.Block [] . M.fromList) [
              (Label "inner", (enscopeExpr . Core.Block []
                . M.fromList) [
                (Label "var", enscopeExpr ((Core.Block [] . M.fromList) [
                  (Label "g",
                    (enscopeExpr . Core.Var . enF . enF . enF) (Priv "y"))
                  ] `Core.Concat` Core.Eval Nothing))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadowing private using path" ~: let
            r = block' [
              env' "outer" #= block' [ self' "g" #= "hello" ],
              self' "inner" #= block' [ env' "outer" #. "g" #= "bye" ]
              ]
            e = (Core.Block [
              (enscopeExpr . Core.Block [] . M.fromList) [
                (Label "g", enscopeExpr (Core.String "hello"))
                ]
              ] . M.fromList) [
              (Label "inner", enscopeExpr (Core.Block [
                enscopeExpr ((Core.Block [] . M.fromList) [
                  (Label "g", enscopeExpr (Core.String "bye"))
                  ] `Core.Concat` Core.liftExpr
                  ((Core.Var . enF . F) (B 0) `Core.Fix`
                    Label "g"))
                ] M.empty))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        ]
    
    , "update" ~: let
        r = (block' [
          self' "a" #= 2,
          self' "b" #= env' "a"
          ] # env' "y")
        e = (Core.Block [] . M.fromList) [
          (Label "a",
            enscopeExpr (Core.Number 2)), 
          (Label "b",
            (enscopeExpr . Core.Var . B) (Label "a"))
          ] `Core.Update` Core.Var (Priv "y")
        in
        parses r >>= assertEqual (banner r) e
      
    , "destructuring" ~: let
        r = block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock' [
            self' "a" #= self' "da",
            self' "b" #= self' "db"
            ] #= env' "obj"
          ]
        e = (Core.Block [
          (enscopeExpr . Core.Block [] . M.fromList) [
            (Label "a", enscopeExpr (Core.Number 2)),
            (Label "b", enscopeExpr (Core.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", enscopeExpr
            ((Core.Var . F) (B 0) `Core.At` Label "a")),
          (Label "db", enscopeExpr
            ((Core.Var . F) (B 0) `Core.At` Label "b"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring unpack" ~: let
        r = block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock'' [ self' "a" #= self' "da" ] (self' "db") #= env' "obj"
          ] #. "b"
        e = (Core.Block [
          (enscopeExpr . Core.Block [] . M.fromList) [
            (Label "a", enscopeExpr (Core.Number 2)),
            (Label "b", enscopeExpr (Core.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", enscopeExpr
            ((Core.Var . F) (B 0) `Core.At` Label "a")),
          (Label "db", enscopeExpr
            ((Core.Var . F) (B 0) `Core.Fix` Label "a"))
          ] `Core.At` Label "b"
        in parses r >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r = block' [
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
        e = (Core.Block [
          (enscopeExpr . Core.Block [] . M.fromList) [
            (Label "a", (enscopeExpr . Core.Block [] 
              . M.fromList) [
              (Label "aa", enscopeExpr (Core.Number 3)),
              (Label "ab", (enscopeExpr . Core.Block []
                . M.fromList) [
                (Label "aba", enscopeExpr (Core.Number 4))
                ])
              ])
            ]
          ] . M.fromList) [
          (Label "da", enscopeExpr
            (((Core.Var . F) (B 0) `Core.At` Label "a") `Core.At`
              Label "aa")),
          (Label "daba", enscopeExpr
            ((((Core.Var . F) (B 0) `Core.At` Label "a") `Core.At`
              Label "ab") `Core.At` Label "aba")),
          (Label "raba", enscopeExpr
            ((((Core.Var . F) (B 0) `Core.At` Label "a") `Core.At`
              Label "ab") `Core.At` Label "aba"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "parent scope binding" ~: let
        r = block' [
          self' "inner" #= 1,
          env' "parInner" #= self' "inner",
          self' "outer" #= block' [
            self' "inner" #= 2,
            self' "a" #= env' "parInner"
            ]
          ]
        e = (Core.Block [
          (enscopeExpr . Core.Var . B) (Label "inner")
          ] . M.fromList) [
          (Label "inner", enscopeExpr (Core.Number 1)),
          (Label "outer", (enscopeExpr . Core.Block [] . M.fromList) [
            (Label "inner", enscopeExpr (Core.Number 2)),
            (Label "a", (enscopeExpr . Core.Var . enF . F) (B 0))
            ])
          ]
        in parses r >>= assertEqual (banner r) e
      
    , "self referencing definition" ~: let
        r = block' [
          env' "y" #= block' [
            self' "a" #= env' "y" #. "b",
            self' "b" #= 1
            ],
          self' "z" #= env' "y" #. "a"
          ]
        e = (Core.Block [
          (enscopeExpr . Core.Block [] . M.fromList) [
            (Label "a", enscopeExpr
              ((Core.Var . enF . F) (B 0) `Core.At` Label "b")),
            (Label "b", enscopeExpr (Core.Number 1))
            ]
          ] . M.fromList) [
            (Label "z", enscopeExpr
              ((Core.Var . F) (B 0) `Core.At` Label "a"))
            ]
        in parses r >>= assertEqual (banner r) e
          
    , "application to referenced outer scope" ~: let
        r = block' [
          env' "y" #= block' [
            self' "a" #= 1,
            env' "b" #= 2,
            self' "x" #= block' [ self' "a" #= env' "b" ]
            ],
          self' "a" #= env' "y" # (env' "y" #. "x") #. "a"
          ]
        e = (Core.Block [
          (enscopeExpr . Core.Block [enscopeExpr (Core.Number 2)] . M.fromList) [
            (Label "a", enscopeExpr (Core.Number 1)),
            (Label "x", (enscopeExpr . Core.Block [] . M.fromList) [
              (Label "a", (enscopeExpr . Core.Var . enF . F) (B 0))
              ])
            ]
          ] . M.fromList) [
          (Label "a", enscopeExpr
            (((Core.Var . F) (B 0) `Core.Update`
              ((Core.Var . F) (B 0) `Core.At` Label "x")) `Core.At`
                Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "application to nested object" ~: let
        r = block' [
          env' "y" #= block' [
            self' "a" #= 1,
            self' "x" #= block' [
              self' "a" #= 2,
              Declare (self' "x")
              ]
            ],
          self' "a" #= env' "y" #. "x" # (env' "y" #. "a")
          ]
        e = (Core.Block [
          (enscopeExpr . Core.Block [] . M.fromList) [
            (Label "a", enscopeExpr (Core.Number 1)),
            (Label "x", (enscopeExpr . Core.Block [] . M.fromList) [
              (Label "a", enscopeExpr (Core.Number 2)),
              (Label "x", enscopeEval (Core.Eval Nothing))
              ])
            ]
          ] . M.fromList) [
          (Label "a", enscopeExpr
            (((Core.Var . F) (B 0) `Core.At` Label "x") `Core.Update`
              ((Core.Var . F) (B 0) `Core.At` Label "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]