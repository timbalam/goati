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
    
    
scopeExpr = Closed . toScope . Member . toScope
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
        r = self_ "public"
        e = (Var . Intern . Pub) (Label "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env_ "private"
        e = (Var . Intern) (Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env_ "var" #. "field"
        e = ((Var . Intern) (Priv "var")
          `At` Label "field")
        in
        parses r >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r = self_ "obj" #. "path" #. "to" #. "value"
        e = ((((Var . Intern . Pub) (Label "obj") 
          `At` Label "path")
          `At` Label "to")
          `At` Label "value")
        in parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "assign public field" ~: let 
          r = Parser.Block [ self_ "public" #= 1 ]
          e = (Block [] . M.fromList) [
            (Label "public", scopeExpr (Number 1))
            ]
          in
          parses r >>= assertEqual (banner r) e
       
        , "assign private field" ~: let
            r = Parser.Block [ env_ "private" #= 1 ]
            e = (Block [scopeExpr (Number 1)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
          
        , "backwards reference" ~: let
            r = Parser.Block [ env_ "one" #= 1, self_ "oneRef" #= env_ "one" ]
            e = (Block [scopeExpr (Number 1)]
              . M.fromList) [
              (Label "oneRef", (scopeExpr . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "forwards reference" ~: let
            r = Parser.Block [ self_ "twoRef" #= env_ "two", env_ "two" #= 2 ]
            e = (Block [scopeExpr (Number 2)]
              . M.fromList) [
              (Label "twoRef", (scopeExpr . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = Parser.Block [ env_ "selfRef" #= env_ "selfRef" ]
            e = (Block [(scopeExpr . Var . F) (B 0)] M.empty)
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = Parser.Block [
              env_ "selfRef" #= env_ "selfRef",
              self_ "loop" #= env_ "selfRef"
              ]
            e = (Block [(scopeExpr . Var . F) (B 0)] . M.fromList) [
              (Label "loop",
                (scopeExpr . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference in private definition" ~: let
            r = Parser.Block [
              self_ "public" #= 1,
              env_ "notPublic" #= self_ "public"
              ]
            e = (Block [
              (scopeExpr . Var . B) (Label "public")
              ]. M.fromList) [
              (Label "public", scopeExpr (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r = Parser.Block [
              self_ "public" #= 1,
              self_ "publicAgain" #= env_ "public"
              ]
            e = (Block []. M.fromList) [
              (Label "public", scopeExpr (Number 1)),
              (Label "publicAgain",
                (scopeExpr . Var . B) (Label "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = Parser.Block [
              env_ "outer" #= 1,
              self_ "object" #= Parser.Block [ self_ "refOuter" #= env_ "outer" ]
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
          
        , "reference global" ~: let
            r = Parser.Block [
              self_ "here" #= 2,
              self_ "refMissing" #= env_ "global"
              ]
            e = (Block [] . M.fromList) [
              (Label "here", scopeExpr (Number 2)),
              (Label "refMissing",
                (scopeExpr . Var . fF . Intern) (Priv "global"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r = Parser.Block [
              self_ "b" #= self_ "a"
              ]
            e = (Block [] . M.fromList) [
              (Label "b",
                (scopeExpr . Var . B) (Label "a"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "pun public assignment" ~: let
            r = Parser.Block [ self_ "b" ]
            e = (Block [] . M.fromList) [
              (Label "b",
                (scopeExpr . Var . fF . Intern . Pub) (Label "b"))
              ]
            in parses r >>= assertEqual (banner r) e
            
            
        , "pun private assignment" ~: let
            r = Parser.Block [ env_ "x" ]
            e = (Block [] . M.fromList) [
              (Label "x",
                (scopeExpr . Var . fF . Intern) (Priv "x"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign to public path" ~: let
            r = Parser.Block [ self_ "a" #. "field" #= 1 ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "field", scopeExpr (Number 1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning path" ~: let
            r = Parser.Block [ self_ "a" #. "f" #= self_ "f" ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "f",
                  (scopeExpr . Var . B) (Label "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning to long path" ~: let
            r = Parser.Block [
              self_ "a" #. "f" #. "g" #= self_ "f" # [ self_ "g" #= self_ "h" ]
              ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "f", (Open . M.fromList) [
                  (Label "g", scopeExpr
                    ((Var . B) (Label "f") `Update`
                      (Block [] . M.fromList) [
                        (Label "g", scopeExpr ((Var . B) (Label "h")))
                        ]))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = Parser.Block [ self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba" ]
            e = (Block [] . M.fromList) [
              (Label "raba", 
                scopeExpr ((((Var . fF . Intern) (Priv "y1")
                    `At` Label "a")
                    `At` Label "ab")
                    `At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r = Parser.Block [
              env_ "y1" #= 1,
              self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba"
              ]
            e = (Block [scopeExpr (Number 1)] . M.fromList) [
              (Label "raba", scopeExpr ((((Var . F) (B 0)
                  `At` Label "a")
                  `At` Label "ab")
                  `At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = Parser.Block [ self_ "a" #. "f" #= env_ "f" ]
            e = (Block [] . M.fromList) [
              (Label "a", (Open . M.fromList) [
                (Label "f",
                  (scopeExpr . Var . fF . Intern) (Priv "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = Parser.Block [ env_ "var" #. "field" #= 2 ]
            e = Block [
              (Open . M.fromList) [
                (Label "field",
                  scopeExpr (Number 2))
                ]
              ] M.empty
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadow private variable" ~: let
            r = Parser.Block [
              env_ "outer" #= 1,
              self_ "inner" #= Parser.Block [
                env_ "outer" #= 2,
                self_ "shadow" #= env_ "outer"
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
            r = Parser.Block [
              self_ "outer" #= "hello",
              self_ "inner" #= Parser.Block [
                self_ "shadow" #= env_ "outer",
                env_ "outer" #= "bye"
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
            r = Parser.Block [
              self_ "inner" #= Parser.Block [
                self_ "var" #. "g" #= env_ "y"
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
            
        , "shadowing private using path ##todo implement" ~: let
            r = Parser.Block [
              env_ "outer" #= Parser.Block [ self_ "g" #= "hello" ],
              self_ "inner" #= Parser.Block [ env_ "outer" #. "g" #= "bye" ]
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
        r = env_ "x" # [ self_ "b" #= env_ "y" ]
        e = (Var . Intern) (Priv "x") `Update` (Block [] . M.fromList) [
          (Label "b", (scopeExpr . Var . fF . Intern) (Priv "y"))
          ]
        in
        parses r >>= assertEqual (banner r) e
      
    , "destructuring" ~: let
        r = Parser.Block [
          Parser.SetBlock [
            self_ "a" #= self_ "oa",
            self_ "b" #= env_ "ob"
            ] #= env_ "o"
          ]
        e = (Block [
          scopeExpr ((Var . fF . Intern) (Priv "o") `At` Label "b")
          ] . M.fromList) [
          (Label "oa", scopeExpr
            ((Var . fF . Intern) (Priv "o") `At` Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring unpack" ~: let
        r = Parser.Block [
          self_ "ob" # [ self_ "a" #= env_ "oa" ] #= env_ "o"
          ]
        e = (Block [
          scopeExpr ((Var . fF . Intern) (Priv "o") `At` Label "a")
          ] . M.fromList) [
          (Label "ob", scopeExpr
            ((Var . fF . Intern) (Priv "o") `Fix` Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun public" ~: let
        r = Parser.Block [
          Parser.SetBlock [ self_ "a" ] #= env_ "o"
          ]
        e = (Block [] . M.fromList) [
          (Label "a",
            scopeExpr ((Var . fF . Intern) (Priv "o") `At` Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun private" ~: let
        r = Parser.Block [
          Parser.SetBlock [ env_ "a" ] #= env_ "o"
          ]
        e = Block [
          scopeExpr ((Var . fF . Intern) (Priv "o") `At` Label "a")
          ] M.empty
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun path" ~: let
        r = Parser.Block [
          Parser.SetBlock [ env_ "a" #. "f" #. "g" ] #= self_ "f"
          ]
        e = Block [
          (Open . M.fromList) [
            (Label "f", (Open . M.fromList) [
              (Label "g", scopeExpr ((((Var . B) (Label "f")
                `At` Label "a")
                `At` Label "f")
                `At` Label "g"))
              ])
            ]
          ] M.empty
        in parses r >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r = Parser.Block [
          Parser.SetBlock [
            self_ "a" #. "aa" #= Parser.SetBlock [ self_ "aaa" #= self_ "oaaa" ]
            ] #= env_ "o"
          ]
        e = (Block [] . M.fromList) [
          (Label "oaaa", scopeExpr
            ((((Var . fF . Intern) (Priv "o")
              `At` Label "a")
              `At` Label "aa")
              `At` Label "aaa"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "enclosing scope binding" ~: let
        r = Parser.Block [
          self_ "var" #= 1,
          env_ "enclosingVar" #= self_ "var",
          self_ "nested" #= Parser.Block [
            self_ "var" #= 2,
            self_ "a" #= env_ "enclosingVar"
            ]
          ]
        e = (Block [
          (scopeExpr . Var . B) (Label "var")
          ] . M.fromList) [
          (Label "var",
            scopeExpr (Number 1)),
          (Label "nested",
            (scopeExpr . Block []
            . M.fromList) [
            (Label "var",
              scopeExpr (Number 2)),
            (Label "a",
              (scopeExpr . Var . fF . F) (B 0))
            ])
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]
        