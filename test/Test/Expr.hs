{-# LANGUAGE OverloadedStrings #-}
module Test.Expr
  ( tests
  )
  where

import qualified Expr
import qualified Types.Expr as Expr
import Types.Classes
import Types.Parser.Short
import Types.Error

import qualified Data.Map as M
import Control.Monad.Trans
import Test.HUnit hiding ( Label )
import Bound --( toScope, Var(..) )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","

parses :: Syntax -> IO (Expr.Expr (Expr.Sym Expr.Vid))
parses =
  either
    (ioError . userError . shows "expr: " . show)
    return
    . Expr.expr
  
  
fails :: (Expr.ExprErrors Expr.Vid -> Assertion) -> Syntax -> Assertion
fails f =
  either f (ioError . userError . shows "HUnit: " . show)
  . Expr.expr
    
    
scopeExpr = Expr.Closed . toScope . Expr.Member . toScope . Expr.Eval . return
scopeEval = Expr.Closed . toScope . Expr.Member . toScope
fF = F . F
    

tests =
  test
    [ "number"  ~: let
        r = 1
        e = (Expr.Number 1)
        in
        parses r >>= assertEqual (banner r) e
           
    , "string" ~: let
        r = "test"
        e = (Expr.String "test")
        in
        parses r >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r = self' "public"
        e = (Expr.Var . Intern . Pub) (Label "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env' "private"
        e = (Expr.Var . Intern) (Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env' "var" #. "field"
        e = ((Expr.Var . Intern) (Priv "var")
          `Expr.At` Label "field")
        in
        parses r >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r = self' "obj" #. "path" #. "to" #. "value"
        e = ((((Expr.Var . Intern . Pub) (Label "obj") 
          `Expr.At` Label "path")
          `Expr.At` Label "to")
          `Expr.At` Label "value")
        in parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "assign public field" ~: let 
          r = block' [ self' "public" #= 1 ]
          e = (Expr.Block [] . M.fromList) [
            (Label "public", scopeExpr (Expr.Number 1))
            ]
          in
          parses r >>= assertEqual (banner r) e
       
        , "assign private field" ~: let
            r = block' [ env' "private" #= 1 ]
            e = (Expr.Block [scopeExpr (Expr.Number 1)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
          
        , "backwards reference" ~: let
            r = block' [ env' "one" #= 1, self' "oneRef" #= env' "one" ]
            e = (Expr.Block [scopeExpr (Expr.Number 1)]
              . M.fromList) [
              (Label "oneRef", (scopeExpr . Expr.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "forwards reference" ~: let
            r = block' [ self' "twoRef" #= env' "two", env' "two" #= 2 ]
            e = (Expr.Block [scopeExpr (Expr.Number 2)]
              . M.fromList) [
              (Label "twoRef", (scopeExpr . Expr.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = block' [ env' "selfRef" #= env' "selfRef" ]
            e = (Expr.Block [(scopeExpr . Expr.Var . F) (B 0)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = block' [
              env' "selfRef" #= env' "selfRef",
              self' "loop" #= env' "selfRef"
              ]
            e = (Expr.Block [(scopeExpr . Expr.Var . F) (B 0)] . M.fromList) [
              (Label "loop",
                (scopeExpr . Expr.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "private referencing public" ~: let
            r = block' [
              self' "public" #= 1,
              env' "notPublic" #= self' "public"
              ]
            e = (Expr.Block [
              (scopeExpr . Expr.Var . B) (Label "public")
              ]. M.fromList) [
              (Label "public", scopeExpr (Expr.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "public referenced as private" ~: let
            r = block' [
              self' "public" #= 1,
              self' "publicAgain" #= env' "public"
              ]
            e = (Expr.Block []. M.fromList) [
              (Label "public", scopeExpr (Expr.Number 1)),
              (Label "publicAgain",
                (scopeExpr . Expr.Var . B) (Label "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "object" #= block' [ self' "refOuter" #= env' "outer" ]
              ]
            e = (Expr.Block [scopeExpr (Expr.Number 1)]
              . M.fromList) [
              (Label "object",
                (scopeExpr . Expr.Block [] . M.fromList) [
                  (Label "refOuter",
                    (scopeExpr . Expr.Var . fF . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "unbound variable" ~: let
            r = block' [
              self' "here" #= 2,
              self' "refMissing" #= env' "missing"
              ]
            e = (Expr.Block [] . M.fromList) [
              (Label "here", scopeExpr (Expr.Number 2)),
              (Label "refMissing",
                (scopeExpr . Expr.Var . fF . Intern) (Priv "missing"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "declared variable" ~: let
            r = block' [
              Declare (self' "unset"),
              self' "set" #= 1
              ]
            e = (Expr.Block [] . M.fromList) [
              (Label "unset", (scopeEval . Expr.Eval . Left . Pub) (Label "unset")),
              (Label "set", scopeExpr (Expr.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference declared variable" ~: let
            r = block' [
              Declare (env' "a"),
              self' "b" #= env' "a"
              ]
            e = (Expr.Block [
              (scopeEval . Expr.Eval . Left) (Priv "a")
              ] . M.fromList) [
              (Label "b",
                (scopeExpr . Expr.Var . F) (B 0))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign public path" ~: let
            r = block' [ self' "a" #. "field" #= 1 ]
            e = (Expr.Block [] . M.fromList) [
              (Label "a", (Expr.Open . M.fromList) [
                (Label "field", scopeExpr (Expr.Number 1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= self' "f" ]
            e = (Expr.Block [] . M.fromList) [
              (Label "a", (Expr.Open . M.fromList) [
                (Label "f",
                  (scopeExpr . Expr.Var . B) (Label "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign expression with public references to long path" ~: let
            r = block' [ self' "a" #. "f" #. "g" #= self' "f" # self' "g" ]
            e = (Expr.Block [] . M.fromList) [
              (Label "a", (Expr.Open . M.fromList) [
                (Label "f", (Expr.Open . M.fromList) [
                  (Label "g", scopeExpr
                    ((Expr.Var . B) (Label "f") `Expr.Update`
                      (Expr.Var . B) (Label "g")))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = block' [ self' "raba" #= env' "y1" #. "a" #. "ab" #. "aba" ]
            e = (Expr.Block [] . M.fromList) [
              (Label "raba", 
                scopeExpr ((((Expr.Var . fF . Intern) (Priv "y1")
                    `Expr.At` Label "a")
                    `Expr.At` Label "ab")
                    `Expr.At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r = block' [
              env' "y1" #= 1,
              self' "raba" #= env' "y1" #. "a" #. "ab" #. "aba"
              ]
            e = (Expr.Block [scopeExpr (Expr.Number 1)] . M.fromList) [
              (Label "raba", scopeExpr ((((Expr.Var . F) (B 0)
                  `Expr.At` Label "a")
                  `Expr.At` Label "ab")
                  `Expr.At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= env' "f" ]
            e = (Expr.Block [] . M.fromList) [
              (Label "a", (Expr.Open . M.fromList) [
                (Label "f",
                  (scopeExpr . Expr.Var . fF . Intern) (Priv "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = block' [ env' "var" #. "field" #= 2 ]
            e = Expr.Block [
              (Expr.Open . M.fromList) [
                (Label "field",
                  scopeExpr (Expr.Number 2))
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
            e = (Expr.Block [
              scopeExpr (Expr.Number 1)
              ] . M.fromList) [
              (Label "inner", (scopeExpr . Expr.Block [
                scopeExpr (Expr.Number 2)
                ] . M.fromList) [
                (Label "shadow", (scopeExpr . Expr.Var . F) (B 0))
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
            e = (Expr.Block [] . M.fromList) [
              (Label "outer",
                scopeExpr (Expr.String "hello")),
              (Label "inner", scopeExpr (((Expr.Block [
                scopeExpr (Expr.String "bye")
                ] . M.fromList) [
                (Label "shadow",
                  (scopeExpr . Expr.Var . F) (B 0))
                ]) `Expr.At` Label "shadow"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "shadowing update public using path" ~: let
            r = block' [
              self' "inner" #= block' [
                self' "var" #. "g" #= env' "y"
                ]
              ]
            e = (Expr.Block [] . M.fromList) [
              (Label "inner", (scopeExpr . Expr.Block []
                . M.fromList) [
                (Label "var", (Expr.Open . M.fromList) [
                  (Label "g", (scopeExpr . Expr.Var . fF
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
            e = (Expr.Block [
              (scopeExpr . Expr.Block [] . M.fromList) [
                (Label "g", scopeExpr (Expr.String "hello"))
                ]
              ] . M.fromList) [
              (Label "inner", scopeExpr (Expr.Block [
                scopeExpr ((Expr.Var . fF . F) (B 0) `Expr.Update` (Expr.Block [] . M.fromList) [
                  (Label "g", scopeExpr (Expr.String "bye"))
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
        e = ((Expr.Block [] . M.fromList) [
          (Label "a",
            scopeExpr (Expr.Number 2)), 
          (Label "b",
            (scopeExpr . Expr.Var . B) (Label "a"))
          ] `Expr.Update` (Expr.Var . Intern) (Priv "y"))
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
        e = (Expr.Block [
          (scopeExpr . Expr.Block [] . M.fromList) [
            (Label "a", scopeExpr (Expr.Number 2)),
            (Label "b", scopeExpr (Expr.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", scopeExpr
            ((Expr.Var . F) (B 0) `Expr.At` Label "a")),
          (Label "db", scopeExpr
            ((Expr.Var . F) (B 0) `Expr.At` Label "b"))
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
        e = ((Expr.Block [
          (scopeExpr . Expr.Block [] . M.fromList) [
            (Label "a", scopeExpr (Expr.Number 2)),
            (Label "b", scopeExpr (Expr.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", scopeExpr
            ((Expr.Var . F) (B 0) `Expr.At` Label "a")),
          (Label "db", scopeExpr
            ((Expr.Var . F) (B 0) `Expr.Fix` Label "a"))
          ] `Expr.At` Label "b")
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
        e = (Expr.Block [
          (scopeExpr . Expr.Block [] . M.fromList) [
            (Label "a", (scopeExpr . Expr.Block [] 
              . M.fromList) [
              (Label "aa", scopeExpr (Expr.Number 3)),
              (Label "ab", (scopeExpr . Expr.Block []
                . M.fromList) [
                (Label "aba", scopeExpr (Expr.Number 4))
                ])
              ])
            ]
          ] . M.fromList) [
          (Label "da", scopeExpr
            (((Expr.Var . F) (B 0)
              `Expr.At` Label "a")
              `Expr.At` Label "aa")),
          (Label "daba", scopeExpr
            ((((Expr.Var . F) (B 0)
              `Expr.At` Label "a")
              `Expr.At` Label "ab")
              `Expr.At` Label "aba")),
          (Label "raba", scopeExpr
            ((((Expr.Var . F) (B 0)
              `Expr.At` Label "a")
              `Expr.At` Label "ab")
              `Expr.At` Label "aba"))
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
        e = (Expr.Block [
          (scopeExpr . Expr.Var . B) (Label "inner")
          ] . M.fromList) [
          (Label "inner",
            scopeExpr (Expr.Number 1)),
          (Label "outer",
            (scopeExpr . Expr.Block []
            . M.fromList) [
            (Label "inner",
              scopeExpr (Expr.Number 2)),
            (Label "a",
              (scopeExpr . Expr.Var . fF . F) (B 0))
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
        e = (Expr.Block [
          (scopeExpr . Expr.Block [] . M.fromList) [
            (Label "a", scopeExpr
              ((Expr.Var . fF . F) (B 0)
                `Expr.At` Label "b")),
            (Label "b", scopeExpr (Expr.Number 1))
            ]
          ] . M.fromList) [
            (Label "z", scopeExpr
              ((Expr.Var . F) (B 0) `Expr.At` Label "a"))
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
        e = (Expr.Block [
          (scopeExpr . Expr.Block [
            scopeExpr (Expr.Number 2)
            ] . M.fromList) [
            (Label "a", scopeExpr (Expr.Number 1)),
            (Label "x", (scopeExpr . Expr.Block []
              . M.fromList) [
              (Label "a", (scopeExpr . Expr.Var . fF . F) (B 0))
              ])
            ]
          ] . M.fromList) [
          (Label "a", scopeExpr
            (((Expr.Var . F) (B 0)
              `Expr.Update` ((Expr.Var . F) (B 0)
                `Expr.At` Label "x"))
              `Expr.At` Label "a"))
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
        e = (Expr.Block [
          (scopeExpr . Expr.Block [] . M.fromList) [
            (Label "a", scopeExpr (Expr.Number 1)),
            (Label "x",
              (scopeExpr . Expr.Block [] . M.fromList) [
              (Label "a",
                scopeExpr (Expr.Number 2)),
              (Label "x",
                (scopeEval . Expr.Eval . Left . Pub) (Label "x"))
              ])
            ]
          ] . M.fromList) [
          (Label "a", scopeExpr
            (((Expr.Var . F) (B 0)
              `Expr.At` Label "x")
              `Expr.Update` ((Expr.Var . F) (B 0)
              `Expr.At` Label "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]