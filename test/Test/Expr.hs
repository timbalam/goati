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
import Control.Exception
import Test.HUnit hiding ( Label )
import Bound --( toScope, Var(..) )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


parses :: Parser.Syntax_ -> IO (Expr ListO (Key Parser.Symbol) Parser.Var)
parses =
  either (ioError . userError . displayException . MyExceptions) return . symexpr "<test>@"
  
  
fails :: (ExprErrors -> Assertion) -> Parser.Syntax_ -> Assertion
fails f = either f (assertFailure . show) . symexpr "<test>@"
    

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
        e = (Var . Parser.Pub) (Parser.Label "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env_ "private"
        e = (Var) (Parser.Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env_ "var" #. "field"
        e = ((Var) (Parser.Priv "var")
          `At` Label "field")
        in
        parses r >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r = self_ "obj" #. "path" #. "to" #. "value"
        e = ((((Var . Parser.Pub) (Parser.Label "obj") 
          `At` Label "path")
          `At` Label "to")
          `At` Label "value")
        in parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "assign public field" ~: let 
          r = Parser.Block [ self_ "public" #= 1 ]
          e = (Block [] . ListO) [
            (Label "public", (Closed . toE) (Number 1))
            ]
          in
          parses r >>= assertEqual (banner r) e
       
        , "assign private field" ~: let
            r = Parser.Block [ env_ "private" #= 1 ]
            e = (Block [(Closed . toE) (Number 1)] (ListO []))
            in
            parses r >>= assertEqual (banner r) e
          
        , "backwards reference" ~: let
            r = Parser.Block [ env_ "one" #= 1, self_ "oneRef" #= env_ "one" ]
            e = (Block [(Closed . toE) (Number 1)]
              . ListO) [
              (Label "oneRef", (Closed . toE . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "forwards reference" ~: let
            r = Parser.Block [ self_ "twoRef" #= env_ "two", env_ "two" #= 2 ]
            e = (Block [(Closed . toE) (Number 2)]
              . ListO) [
              (Label "twoRef", (Closed . toE . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = Parser.Block [ env_ "selfRef" #= env_ "selfRef" ]
            e = (Block [(Closed . toE . Var . F) (B 0)] (ListO []))
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = Parser.Block [
              env_ "selfRef" #= env_ "selfRef",
              self_ "loop" #= env_ "selfRef"
              ]
            e = (Block [(Closed . toE . Var . F) (B 0)] . ListO) [
              (Label "loop",
                (Closed . toE . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference in private definition" ~: let
            r = Parser.Block [
              self_ "public" #= 1,
              env_ "notPublic" #= self_ "public"
              ]
            e = (Block [
              (Closed . toE . Var . B) (Label "public")
              ]. ListO) [
              (Label "public", (Closed . toE) (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r = Parser.Block [
              self_ "public" #= 1,
              self_ "publicAgain" #= env_ "public"
              ]
            e = (Block []. ListO) [
              (Label "public", (Closed . toE) (Number 1)),
              (Label "publicAgain",
                (Closed . toE . Var . B) (Label "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = Parser.Block [
              env_ "outer" #= 1,
              self_ "object" #= Parser.Block [ self_ "refOuter" #= env_ "outer" ]
              ]
            e = (Block [(Closed . toE) (Number 1)]
              . ListO) [
              (Label "object",
                (Closed . toE . Block [] . ListO) [
                  (Label "refOuter",
                    (Closed . toE . Var . F . F . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "reference global" ~: let
            r = Parser.Block [
              self_ "here" #= 2,
              self_ "refMissing" #= env_ "global"
              ]
            e = (Block [] . ListO) [
              (Label "here", (Closed . toE) (Number 2)),
              (Label "refMissing",
                (Closed . toE . Var . F . F) (Parser.Priv "global"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r = Parser.Block [
              self_ "b" #= self_ "a"
              ]
            e = (Block [] . ListO) [
              (Label "b",
                (Closed . toE . Var . B) (Label "a"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "pun public assignment to introduce private reference" ~: let
            r = Parser.Block [ self_ "b" ]
            e = Block [(Closed . toE . Var . B) (Label "b")] (ListO [])
            in parses r >>= assertEqual (banner r) e
            
            
        , "pun private assignment to introduce public reference enclosing private" ~: let
            r = Parser.Block [ env_ "x" ]
            e = (Block [] . ListO) [
              (Label "x",
                (Closed . toE . Var . F . F) (Parser.Priv "x"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign to public path" ~: let
            r = Parser.Block [ self_ "a" #. "field" #= 1 ]
            e = (Block [] . ListO) [
              (Label "a", (Open . ListO) [
                (Label "field", (Closed . toE) (Number 1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning path" ~: let
            r = Parser.Block [ self_ "a" #. "f" #= self_ "f" ]
            e = (Block [] . ListO) [
              (Label "a", (Open . ListO) [
                (Label "f",
                  (Closed . toE . Var . B) (Label "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning to long path" ~: let
            r = Parser.Block [
              self_ "a" #. "f" #. "g" #= self_ "f" # [ self_ "g" #= self_ "h" ]
              ]
            e = (Block [] . ListO) [
              (Label "a", (Open . ListO) [
                (Label "f", (Open . ListO) [
                  (Label "g", (Closed . toE)
                    ((Var . B) (Label "f") `Update`
                      (Block [] . ListO) [
                        (Label "g", (Closed . toE) ((Var . B) (Label "h")))
                        ]))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = Parser.Block [ self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba" ]
            e = (Block [] . ListO) [
              (Label "raba", 
                (Closed . toE) ((((Var . F . F) (Parser.Priv "y1")
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
            e = (Block [(Closed . toE) (Number 1)] . ListO) [
              (Label "raba", (Closed . toE) ((((Var . F) (B 0)
                  `At` Label "a")
                  `At` Label "ab")
                  `At` Label "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = Parser.Block [ self_ "a" #. "f" #= env_ "f" ]
            e = (Block [] . ListO) [
              (Label "a", (Open . ListO) [
                (Label "f",
                  (Closed . toE . Var . F . F) (Parser.Priv "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = Parser.Block [ env_ "var" #. "field" #= 2 ]
            e = Block [
              (Open . ListO) [
                (Label "field",
                  (Closed . toE) (Number 2))
                ]
              ] (ListO [])
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
              (Closed . toE) (Number 1)
              ] . ListO) [
              (Label "inner", (Closed . toE . Block [
                (Closed . toE) (Number 2)
                ] . ListO) [
                (Label "shadow", (Closed . toE . Var . F) (B 0))
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
            e = (Block [] . ListO) [
              (Label "outer",
                (Closed . toE) (String "hello")),
              (Label "inner", (Closed . toE) (((Block [
                (Closed . toE) (String "bye")
                ] . ListO) [
                (Label "shadow",
                  (Closed . toE . Var . F) (B 0))
                ]) `At` Label "shadow"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "shadowing update public using path" ~: let
            r = Parser.Block [
              self_ "inner" #= Parser.Block [
                self_ "var" #. "g" #= env_ "y"
                ]
              ]
            e = (Block [] . ListO) [
              (Label "inner", (Closed . toE . Block []
                . ListO) [
                (Label "var", (Open . ListO) [
                  (Label "g", (Closed . toE . Var . F . F
                    . F . F) (Parser.Priv "y"))
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
              (Closed . toE . Block [] . ListO) [
                (Label "g", (Closed . toE) (String "hello"))
                ]
              ] . ListO) [
              (Label "inner", (Closed . toE) (Block [
                (Closed . toE) ((Var . F . F . F) (B 0) `Update` (Block [] . ListO) [
                  (Label "g", (Closed . toE) (String "bye"))
                  ])
                ] (ListO [])))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        ]
    
    , "update" ~: let
        r = env_ "x" # [ self_ "b" #= env_ "y" ]
        e = (Var) (Parser.Priv "x") `Update` (Block [] . ListO) [
          (Label "b", (Closed . toE . Var . F . F) (Parser.Priv "y"))
          ]
        in
        parses r >>= assertEqual (banner r) e
        
    , "operation sugar" ~:
        [ "add" ~: let
            r = env_ "x" #+ env_ "y"
            e = ((Var (Parser.Priv "x") `At` Binop Add)  `Update`
              (Block [] . ListO) [
              (Label "x", (Closed . toE . Var . F . F) (Parser.Priv "y"))
              ]) `At` Label "return"
            in
            parses r >>= assertEqual (banner r) e
          
        , "not" ~: let
            r = not_ (env_ "x")
            e = Var (Parser.Priv "x") `At` Unop Not
            in parses r >>= assertEqual (banner r) e
          
        ]
      
    , "destructuring" ~: let
        r = Parser.Block [
          Parser.SetBlock [
            self_ "a" #= self_ "oa",
            self_ "b" #= env_ "ob"
            ] #= env_ "o"
          ]
        e = (Block [
          (Closed . toE) ((Var . F . F) (Parser.Priv "o") `At` Label "b")
          ] . ListO) [
          (Label "oa", (Closed . toE)
            ((Var . F . F) (Parser.Priv "o") `At` Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "destructuring unpack" ~: let
        r = Parser.Block [
          [ self_ "a" #= env_ "oa" ] #... self_ "ob" #= env_ "o"
          ]
        e = (Block [
          (Closed . toE) ((Var . F . F) (Parser.Priv "o") `At` Label "a")
          ] . ListO) [
          (Label "ob", (Closed . toE)
            ((Var . F . F) (Parser.Priv "o") `Fix` Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring unpack with paths" ~: let
        r = Parser.Block [
          [ self_ "f" #. "g" #= env_ "set" ] #... self_ "rem" #= env_ "get"
          ]
        e = (Block [
          (Closed . toE) (((Var . F . F) (Parser.Priv "get") `At` Label "f") `At` Label "g")
          ] . ListO) [
          (Label "rem", (Closed . toE)
            (((Var . F . F) (Parser.Priv "get") `Fix` Label "f") `Fix` Label "g"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "destructuring pun public" ~: let
        r = Parser.Block [
          Parser.SetBlock [ self_ "a" ] #= env_ "o"
          ]
        e = (Block [] . ListO) [
          (Label "a",
            (Closed . toE) ((Var . F . F) (Parser.Priv "o") `At` Label "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun private" ~: let
        r = Parser.Block [
          Parser.SetBlock [ env_ "a" ] #= env_ "o"
          ]
        e = Block [
          (Closed . toE) ((Var . F . F) (Parser.Priv "o") `At` Label "a")
          ] (ListO [])
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun path" ~: let
        r = Parser.Block [
          Parser.SetBlock [ env_ "a" #. "f" #. "g" ] #= self_ "f"
          ]
        e = Block [
          (Open . ListO) [
            (Label "f", (Open . ListO) [
              (Label "g", (Closed . toE) ((((Var . B) (Label "f")
                `At` Label "a")
                `At` Label "f")
                `At` Label "g"))
              ])
            ]
          ] (ListO []) 
        in parses r >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r = Parser.Block [
          Parser.SetBlock [
            self_ "a" #. "aa" #= Parser.SetBlock [ self_ "aaa" #= self_ "oaaa" ]
            ] #= env_ "o"
          ]
        e = (Block [] . ListO) [
          (Label "oaaa", (Closed . toE)
            ((((Var . F . F) (Parser.Priv "o")
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
          (Closed . toE . Var . B) (Label "var")
          ] . ListO) [
          (Label "var",
            (Closed . toE) (Number 1)),
          (Label "nested",
            (Closed . toE . Block []
            . ListO) [
            (Label "var",
              (Closed . toE) (Number 2)),
            (Label "a",
              (Closed . toE . Var . F . F . F) (B 0))
            ])
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]
        