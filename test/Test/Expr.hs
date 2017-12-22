{-# LANGUAGE OverloadedStrings #-}
module Test.Expr
  ( tests
  )
  where

import qualified Expr
import qualified Types.Expr as Expr
import Types.Expr( liftVal, liftExpr )
import Types.Classes
import Types.Parser.Short
import Types.Error

import qualified Data.Map as M
import Control.Monad.Trans
import Test.HUnit hiding ( Label )
import Bound --( toScope, Var(..) )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","

parses :: Syntax -> IO (Expr.Expr' Expr.Vid)
parses =
  either
    (ioError . userError . shows "expr: " . show)
    return
    . Expr.expr
  
  
fails :: (Expr.ExprErrors Expr.Vid -> Assertion) -> Syntax -> Assertion
fails f =
  either f (ioError . userError . shows "HUnit: " . show)
  . Expr.expr
    
    
enscopeVal = Expr.Enscope . toScope . toScope . Expr.liftVal
enscopeExpr = Expr.Enscope . toScope . toScope . Expr.liftExpr
enscopeEval = Expr.Enscope . toScope . toScope
enF = F . F
    

tests =
  test
    [ "number"  ~: let
        r = 1
        e = Expr.Val (Expr.Number 1)
        in
        parses r >>= assertEqual (banner r) e
           
    , "string" ~: let
        r = "test"
        e = Expr.Val (Expr.String "test")
        in
        parses r >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r = self' "public"
        e = (Expr.Var . Pub) (Label "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env' "private"
        e = Expr.Var (Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env' "var" #. "field"
        e = Expr.Val (return (Priv "var") `Expr.At` Label "field")
        in
        parses r >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r = self' "obj" #. "path" #. "to" #. "value"
        e = Expr.Val (liftVal (liftVal
          ((return . Pub) (Label "obj") 
          `Expr.At` Label "path")
          `Expr.At` Label "to")
          `Expr.At` Label "value")
        in parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "assign public field" ~: let 
          r = block' [ self' "public" #= 1 ]
          e = (Expr.Val . Expr.Block [] . M.fromList) [
            (Label "public", enscopeVal (Expr.Number 1))
            ]
          in
          parses r >>= assertEqual (banner r) e
       
        , "assign private field" ~: let
            r = block' [ env' "private" #= 1 ]
            e = Expr.Val (Expr.Block [enscopeVal (Expr.Number 1)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
          
        , "backwards reference" ~: let
            r = block' [ env' "one" #= 1, self' "oneRef" #= env' "one" ]
            e = (Expr.Val . Expr.Block [enscopeVal (Expr.Number 1)]
              . M.fromList) [
              (Label "oneRef", (enscopeExpr . Expr.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "forwards reference" ~: let
            r = block' [ self' "twoRef" #= env' "two", env' "two" #= 2 ]
            e = (Expr.Val . Expr.Block [enscopeVal (Expr.Number 2)]
              . M.fromList) [
              (Label "twoRef", (enscopeExpr . Expr.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = block' [ env' "selfRef" #= env' "selfRef" ]
            e = Expr.Val (Expr.Block [(enscopeExpr . Expr.Var . F) (B 0)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = block' [
              env' "selfRef" #= env' "selfRef",
              self' "loop" #= env' "selfRef"
              ]
            e = (Expr.Val . Expr.Block [(enscopeExpr . Expr.Var . F) (B 0)] . M.fromList) [
              (Label "loop",
                (enscopeExpr . Expr.Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "private referencing public" ~: let
            r = block' [
              self' "public" #= 1,
              env' "notPublic" #= self' "public"
              ]
            e = (Expr.Val . Expr.Block [
              (enscopeExpr . Expr.Var . B) (Label "public")
              ]. M.fromList) [
              (Label "public", enscopeVal (Expr.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "public referenced as private" ~: let
            r = block' [
              self' "public" #= 1,
              self' "publicAgain" #= env' "public"
              ]
            e = (Expr.Val . Expr.Block []. M.fromList) [
              (Label "public", enscopeVal (Expr.Number 1)),
              (Label "publicAgain",
                (enscopeExpr . Expr.Var . B) (Label "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block' [
              env' "outer" #= 1,
              self' "object" #= block' [ self' "refOuter" #= env' "outer" ]
              ]
            e = (Expr.Val . Expr.Block [enscopeVal (Expr.Number 1)]
              . M.fromList) [
              (Label "object",
                (enscopeVal . Expr.Block [] . M.fromList) [
                  (Label "refOuter",
                    (enscopeExpr . Expr.Var . enF . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "unbound variable" ~: let
            r = block' [
              self' "here" #= 2,
              self' "refMissing" #= env' "missing"
              ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "here", enscopeVal (Expr.Number 2)),
              (Label "refMissing",
                (enscopeExpr . Expr.Var . enF) (Priv "missing"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "declared variable" ~: let
            r = block' [
              Declare (self' "unset"),
              self' "set" #= 1
              ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "unset", (enscopeEval . Expr.Eval . Left . Pub) (Label "unset")),
              (Label "set", enscopeVal (Expr.Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference declared variable" ~: let
            r = block' [
              Declare (env' "a"),
              self' "b" #= env' "a"
              ]
            e = (Expr.Val . Expr.Block [
              (enscopeEval . Expr.Eval . Left) (Priv "a")
              ] . M.fromList) [
              (Label "b",
                (enscopeExpr . Expr.Var . F) (B 0))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign public path" ~: let
            r = block' [ self' "a" #. "field" #= 1 ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "a", (enscopeVal
                . Expr.Block [] . M.fromList) [
                (Label "field", enscopeVal (Expr.Number 1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= self' "f" ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "a", (enscopeVal
                . Expr.Block [] . M.fromList) [
                (Label "f",
                  (enscopeExpr . Expr.Var . enF . B) (Label "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign expression with public references to long path" ~: let
            r = block' [ self' "a" #. "f" #. "g" #= self' "f" # self' "g" ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "a", (enscopeVal
                . Expr.Block [] . M.fromList) [
                (Label "f", (enscopeVal
                  . Expr.Block [] . M.fromList) [
                  (Label "g", enscopeVal
                    ((liftExpr . Expr.Var . enF . enF . B) (Label "f") `Expr.Update`
                      (liftExpr . Expr.Var . enF . enF . B) (Label "g")))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = block' [ self' "raba" #= env' "y1" #. "a" #. "ab" #. "aba" ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "raba", 
                enscopeVal (liftVal (liftVal
                  ((liftExpr . Expr.Var . enF) (Priv "y1")
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
            e = (Expr.Val . Expr.Block [enscopeVal (Expr.Number 1)] . M.fromList) [
              (Label "raba", enscopeVal (liftVal
                (liftVal ((liftExpr . Expr.Var . F) (B 0)
                  `Expr.At` Label "a")
                  `Expr.At` Label "ab")
                  `Expr.At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block' [ self' "a" #. "f" #= env' "f" ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "a",
                (enscopeVal . Expr.Block []
                . M.fromList) [
                (Label "f",
                  (enscopeExpr . Expr.Var . enF . enF) (Priv "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = block' [ env' "var" #. "field" #= 2 ]
            e = Expr.Val (Expr.Block [
              enscopeVal ((liftVal . Expr.Block [] . M.fromList) [
                (Label "field",
                  enscopeVal (Expr.Number 2))
                ] `Expr.Concat`
                ((Expr.Var . enF) (Priv "var") `Expr.Fix`
                  Label "field"))
              ] M.empty)
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
            e = (Expr.Val . Expr.Block [
              enscopeVal (Expr.Number 1)
              ] . M.fromList) [
              (Label "inner", (enscopeVal . Expr.Block [
                enscopeVal (Expr.Number 2)
                ] . M.fromList) [
                (Label "shadow", (enscopeExpr . Expr.Var . F) (B 0))
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
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "outer",
                enscopeVal (Expr.String "hello")),
              (Label "inner", enscopeVal (((liftVal . Expr.Block [
                enscopeVal (Expr.String "bye")
                ] . M.fromList) [
                (Label "shadow",
                  (enscopeExpr . Expr.Var . F) (B 0))
                ]) `Expr.At` Label "shadow"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "shadowing update public using path" ~: let
            r = block' [
              self' "inner" #= block' [
                self' "var" #. "g" #= env' "y"
                ]
              ]
            e = (Expr.Val . Expr.Block [] . M.fromList) [
              (Label "inner", (enscopeVal . Expr.Block []
                . M.fromList) [
                (Label "var", (enscopeVal . Expr.Block [] . M.fromList) [
                  (Label "g", (enscopeExpr . Expr.Var . enF
                    . enF . enF) (Priv "y"))
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
            e = (Expr.Val . Expr.Block [
              (enscopeVal . Expr.Block [] . M.fromList) [
                (Label "g", enscopeVal (Expr.String "hello"))
                ]
              ] . M.fromList) [
              (Label "inner", enscopeVal (Expr.Block [
                enscopeVal ((liftVal . Expr.Block [] . M.fromList) [
                  (Label "g", enscopeVal (Expr.String "bye"))
                  ] `Expr.Concat` 
                  ((Expr.Var . enF . F) (B 0) `Expr.Fix`
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
        e = Expr.Val ((liftVal . Expr.Block [] . M.fromList) [
          (Label "a",
            enscopeVal (Expr.Number 2)), 
          (Label "b",
            (enscopeExpr . Expr.Var . B) (Label "a"))
          ] `Expr.Update` (liftExpr . Expr.Var) (Priv "y"))
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
        e = (Expr.Val . Expr.Block [
          (enscopeVal . Expr.Block [] . M.fromList) [
            (Label "a", enscopeVal (Expr.Number 2)),
            (Label "b", enscopeVal (Expr.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", enscopeVal
            ((liftExpr . Expr.Var . F) (B 0) `Expr.At` Label "a")),
          (Label "db", enscopeVal
            ((liftExpr . Expr.Var . F) (B 0) `Expr.At` Label "b"))
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
        e = Expr.Val ((liftVal . Expr.Block [
          (enscopeVal . Expr.Block [] . M.fromList) [
            (Label "a", enscopeVal (Expr.Number 2)),
            (Label "b", enscopeVal (Expr.Number 3))
            ]
          ] . M.fromList) [
          (Label "da", enscopeVal
            ((liftExpr . Expr.Var . F) (B 0) `Expr.At` Label "a")),
          (Label "db", enscopeExpr
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
        e = (Expr.Val . Expr.Block [
          (enscopeVal . Expr.Block [] . M.fromList) [
            (Label "a", (enscopeVal . Expr.Block [] 
              . M.fromList) [
              (Label "aa", enscopeVal (Expr.Number 3)),
              (Label "ab", (enscopeVal . Expr.Block []
                . M.fromList) [
                (Label "aba", enscopeVal (Expr.Number 4))
                ])
              ])
            ]
          ] . M.fromList) [
          (Label "da", enscopeVal
            (liftVal ((liftExpr . Expr.Var . F) (B 0)
              `Expr.At` Label "a")
              `Expr.At` Label "aa")),
          (Label "daba", enscopeVal
            (liftVal (liftVal ((liftExpr . Expr.Var . F) (B 0)
              `Expr.At` Label "a")
              `Expr.At` Label "ab")
              `Expr.At` Label "aba")),
          (Label "raba", enscopeVal
            (liftVal (liftVal ((liftExpr . Expr.Var . F) (B 0)
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
        e = (Expr.Val . Expr.Block [
          (enscopeExpr . Expr.Var . B) (Label "inner")
          ] . M.fromList) [
          (Label "inner",
            enscopeVal (Expr.Number 1)),
          (Label "outer",
            (enscopeVal . Expr.Block []
            . M.fromList) [
            (Label "inner",
              enscopeVal (Expr.Number 2)),
            (Label "a",
              (enscopeExpr . Expr.Var . enF . F) (B 0))
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
        e = (Expr.Val . Expr.Block [
          (enscopeVal . Expr.Block [] . M.fromList) [
            (Label "a", enscopeVal
              ((liftExpr . Expr.Var . enF . F) (B 0)
                `Expr.At` Label "b")),
            (Label "b", enscopeVal (Expr.Number 1))
            ]
          ] . M.fromList) [
            (Label "z", enscopeVal
              ((liftExpr . Expr.Var . F) (B 0) `Expr.At` Label "a"))
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
        e = (Expr.Val . Expr.Block [
          (enscopeVal . Expr.Block [
            enscopeVal (Expr.Number 2)
            ] . M.fromList) [
            (Label "a", enscopeVal (Expr.Number 1)),
            (Label "x", (enscopeVal . Expr.Block []
              . M.fromList) [
              (Label "a", (enscopeExpr . Expr.Var . enF . F) (B 0))
              ])
            ]
          ] . M.fromList) [
          (Label "a", enscopeVal
            (liftVal ((liftExpr . Expr.Var . F) (B 0)
              `Expr.Update` liftVal ((liftExpr . Expr.Var . F) (B 0)
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
        e = (Expr.Val . Expr.Block [
          (enscopeVal . Expr.Block [] . M.fromList) [
            (Label "a", enscopeVal (Expr.Number 1)),
            (Label "x",
              (enscopeVal . Expr.Block [] . M.fromList) [
              (Label "a",
                enscopeVal (Expr.Number 2)),
              (Label "x",
                (enscopeEval . Expr.Eval . Left . Pub) (Label "x"))
              ])
            ]
          ] . M.fromList) [
          (Label "a", enscopeVal
            (liftVal ((liftExpr . Expr.Var . F) (B 0)
              `Expr.At` Label "x")
              `Expr.Update` liftVal ((liftExpr . Expr.Var . F) (B 0)
              `Expr.At` Label "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]