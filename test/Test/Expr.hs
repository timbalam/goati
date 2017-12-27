{-# LANGUAGE OverloadedStrings #-}
module Test.Expr
  ( tests
  )
  where

import Expr
import Types.Expr
import Types.Classes
import Types.Parser.Short
import qualified Types.Parser as Parser
import Types.Error

import qualified Data.Map as M
import Control.Monad.Trans
import Test.HUnit hiding ( Label )
import Bound --( toScope, Var(..) )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","

parses :: Parser.Syntax -> IO (Expr (Sym Vid))
parses =
  either throwList return . expr
  
  
fails :: (ExprErrors Vid -> Assertion) -> Parser.Syntax -> Assertion
fails f =
  either f (ioError . userError . shows "HUnit: " . show)
  . expr
    
    
scopeExpr = Closed . toScope . Member . toScope . Eval . return
scopeEval = Closed . toScope . Member . toScope
fF = F . F
    

tests =
  test
    [ "number"  ~: let
        r = 1
        e = (Number 1)
        in
        parses r >>= assertEqual (banner r) e
           
    , "string" ~: let
        r = "test"
        e = (String "test")
        in
        parses r >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r = self' "public"
        e = (Var . Intern . Pub) (Label "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env' "private"
        e = (Var . Intern) (Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env' "var" #. "field"
        e = ((Var . Intern) (Priv "var")
          `At` Label "field")
        in
        parses r >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r = self' "obj" #. "path" #. "to" #. "value"
        e = ((((Var . Intern . Pub) (Label "obj") 
          `At` Label "path")
          `At` Label "to")
          `At` Label "value")
        in parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "assign public field" ~: let 
          r = block' [ self' "public" #= 1 ]
          e = (Block [] . M.fromList) [
            (Label "public", scopeExpr (Number 1))
            ]
          in
          parses r >>= assertEqual (banner r) e
       
        , "assign private field" ~: let
            r = block' [ env' "private" #= 1 ]
            e = (Block [scopeExpr (Number 1)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
          
        , "backwards reference" ~: let
            r = block' [ env' "one" #= 1, self' "oneRef" #= env' "one" ]
            e = (Block [scopeExpr (Number 1)]
              . M.fromList) [
              (Label "oneRef", (scopeExpr . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "forwards reference" ~: let
            r = block' [ self' "twoRef" #= env' "two", env' "two" #= 2 ]
            e = (Block [scopeExpr (Number 2)]
              . M.fromList) [
              (Label "twoRef", (scopeExpr . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = block' [ env' "selfRef" #= env' "selfRef" ]
            e = (Block [(scopeExpr . Var . F) (B 0)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = block' [
              env' "selfRef" #= env' "selfRef",
              self' "loop" #= env' "selfRef"
              ]
            e = (Block [(scopeExpr . Var . F) (B 0)] . M.fromList) [
              (Label "loop",
                (scopeExpr . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "private referencing public" ~: let
            r = block' [
              self' "public" #= 1,
              env' "notPublic" #= self' "public"
              ]
            e = (Block [
              (scopeExpr . Var . B) (Label "public")
              ]. M.fromList) [
              (Label "public", scopeExpr (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "public referenced as private" ~: let
            r = block' [
              self' "public" #= 1,
              self' "publicAgain" #= env' "public"
              ]
            e = (Block []. M.fromList) [
              (Label "public", scopeExpr (Number 1)),
              (Label "publicAgain",
                (scopeExpr . Var . B) (Label "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "object" #= block' [ self' "refOuter" #= env' "outer" ]
              ]
            e = (Block [scopeExpr (Number 1)]
              . M.fromList) [
              (Label "object",
                (scopeExpr . Block [] . M.fromList) [
                  (Label "refOuter",
                    (scopeExpr . Var . fF . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "unbound variable" ~: let
            r = block' [
              self' "here" #= 2,
              self' "refMissing" #= env' "missing"
              ]
            e = (Block [] . M.fromList) [
              (Label "here", scopeExpr (Number 2)),
              (Label "refMissing",
                (scopeExpr . Var . fF . Intern) (Priv "missing"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "declared variable" ~: let
            r = block' [
              Parser.Declare (self' "unset"),
              self' "set" #= 1
              ]
            e = (Block [] . M.fromList) [
              (Label "unset", (scopeEval . Eval . Left . Pub) (Label "unset")),
              (Label "set", scopeExpr (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference declared variable" ~: let
            r = block' [
              Parser.Declare (env' "a"),
              self' "b" #= env' "a"
              ]
            e = (Block [
              (scopeEval . Eval . Left) (Priv "a")
              ] . M.fromList) [
              (Label "b",
                (scopeExpr . Var . F) (B 0))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign public path" ~: let
            r = block' [ self' "a" #. "field" #= 1 ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "field", scopeExpr (Number 1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= self' "f" ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "f",
                  (scopeExpr . Var . B) (Label "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign expression with public references to long path" ~: let
            r = block' [ self' "a" #. "f" #. "g" #= self' "f" # self' "g" ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "f", (Open . M.fromList) [
                  (Label "g", scopeExpr
                    ((Var . B) (Label "f") `Update`
                      (Var . B) (Label "g")))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = block' [ self' "raba" #= env' "y1" #. "a" #. "ab" #. "aba" ]
            e = (Block [] . M.fromList) [
              (Label "raba", 
                scopeExpr ((((Var . fF . Intern) (Priv "y1")
                    `At` Label "a")
                    `At` Label "ab")
                    `At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r = block' [
              env' "y1" #= 1,
              self' "raba" #= env' "y1" #. "a" #. "ab" #. "aba"
              ]
            e = (Block [scopeExpr (Number 1)] . M.fromList) [
              (Label "raba", scopeExpr ((((Var . F) (B 0)
                  `At` Label "a")
                  `At` Label "ab")
                  `At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= env' "f" ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "f",
                  (scopeExpr . Var . fF . Intern) (Priv "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = block' [ env' "var" #. "field" #= 2 ]
            e = Block [
              (Open . M.fromList) [
                (Label "field",
                  scopeExpr (Number 2))
                ]
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
            e = (Block [
              scopeExpr (Number 1)
              ] . M.fromList) [
              (Label "inner", (scopeExpr . Block [
                scopeExpr (Number 2)
                ] . M.fromList) [
                (Label "shadow", (scopeExpr . Var . F) (B 0))
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
            e = (Block [] . M.fromList) [
              (Label "outer",
                scopeExpr (String "hello")),
              (Label "inner", scopeExpr (((Block [
                scopeExpr (String "bye")
                ] . M.fromList) [
                (Label "shadow",
                  (scopeExpr . Var . F) (B 0))
                ]) `At` Label "shadow"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "shadowing update public using path" ~: let
            r = block' [
              self' "inner" #= block' [
                self' "var" #. "g" #= env' "y"
                ]
              ]
            e = (Block [] . M.fromList) [
              (Label "inner", (scopeExpr . Block []
                . M.fromList) [
                (Label "var", (Open . M.fromList) [
                  (Label "g", (scopeExpr . Var . fF
                    . fF . Intern) (Priv "y"))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadowing private using path" ~: let
            r = block' [
              env' "outer" #= block' [ self' "g" #= "hello" ],
              self' "inner" #= block' [ env' "outer" #. "g" #= "bye" ]
              ]
            e = (Block [
              (scopeExpr . Block [] . M.fromList) [
                (Label "g", scopeExpr (String "hello"))
                ]
              ] . M.fromList) [
              (Label "inner", scopeExpr (Block [
                scopeExpr ((Var . fF . F) (B 0) `Update` (Block [] . M.fromList) [
                  (Label "g", scopeExpr (String "bye"))
                  ])
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
        e = ((Block [] . M.fromList) [
          (Label "a",
            scopeExpr (Number 2)), 
          (Label "b",
            (scopeExpr . Var . B) (Label "a"))
          ] `Update` (Var . Intern) (Priv "y"))
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
        e = (Block [
          (scopeExpr . Block [] . M.fromList) [
            (Label "a", scopeExpr (Number 2)),
            (Label "b", scopeExpr (Number 3))
            ]
          ] . M.fromList) [
          (Label "da", scopeExpr
            ((Var . F) (B 0) `At` Label "a")),
          (Label "db", scopeExpr
            ((Var . F) (B 0) `At` Label "b"))
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
        e = ((Block [
          (scopeExpr . Block [] . M.fromList) [
            (Label "a", scopeExpr (Number 2)),
            (Label "b", scopeExpr (Number 3))
            ]
          ] . M.fromList) [
          (Label "da", scopeExpr
            ((Var . F) (B 0) `At` Label "a")),
          (Label "db", scopeExpr
            ((Var . F) (B 0) `Fix` Label "a"))
          ] `At` Label "b")
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
        e = (Block [
          (scopeExpr . Block [] . M.fromList) [
            (Label "a", (scopeExpr . Block [] 
              . M.fromList) [
              (Label "aa", scopeExpr (Number 3)),
              (Label "ab", (scopeExpr . Block []
                . M.fromList) [
                (Label "aba", scopeExpr (Number 4))
                ])
              ])
            ]
          ] . M.fromList) [
          (Label "da", scopeExpr
            (((Var . F) (B 0)
              `At` Label "a")
              `At` Label "aa")),
          (Label "daba", scopeExpr
            ((((Var . F) (B 0)
              `At` Label "a")
              `At` Label "ab")
              `At` Label "aba")),
          (Label "raba", scopeExpr
            ((((Var . F) (B 0)
              `At` Label "a")
              `At` Label "ab")
              `At` Label "aba"))
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
        e = (Block [
          (scopeExpr . Var . B) (Label "inner")
          ] . M.fromList) [
          (Label "inner",
            scopeExpr (Number 1)),
          (Label "outer",
            (scopeExpr . Block []
            . M.fromList) [
            (Label "inner",
              scopeExpr (Number 2)),
            (Label "a",
              (scopeExpr . Var . fF . F) (B 0))
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
        e = (Block [
          (scopeExpr . Block [] . M.fromList) [
            (Label "a", scopeExpr
              ((Var . fF . F) (B 0)
                `At` Label "b")),
            (Label "b", scopeExpr (Number 1))
            ]
          ] . M.fromList) [
            (Label "z", scopeExpr
              ((Var . F) (B 0) `At` Label "a"))
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
        e = (Block [
          (scopeExpr . Block [
            scopeExpr (Number 2)
            ] . M.fromList) [
            (Label "a", scopeExpr (Number 1)),
            (Label "x", (scopeExpr . Block []
              . M.fromList) [
              (Label "a", (scopeExpr . Var . fF . F) (B 0))
              ])
            ]
          ] . M.fromList) [
          (Label "a", scopeExpr
            (((Var . F) (B 0)
              `Update` ((Var . F) (B 0)
                `At` Label "x"))
              `At` Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "application to nested object" ~: let
        r = block' [
          env' "y" #= block' [
            self' "a" #= 1,
            self' "x" #= block' [
              self' "a" #= 2,
              Parser.Declare (self' "x")
              ]
            ],
          self' "a" #= env' "y" #. "x" # (env' "y" #. "a")
          ]
        e = (Block [
          (scopeExpr . Block [] . M.fromList) [
            (Label "a", scopeExpr (Number 1)),
            (Label "x",
              (scopeExpr . Block [] . M.fromList) [
              (Label "a",
                scopeExpr (Number 2)),
              (Label "x",
                (scopeEval . Eval . Left . Pub) (Label "x"))
              ])
            ]
          ] . M.fromList) [
          (Label "a", scopeExpr
            (((Var . F) (B 0)
              `At` Label "x")
              `Update` ((Var . F) (B 0)
              `At` Label "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]