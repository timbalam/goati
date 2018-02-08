{-# LANGUAGE OverloadedStrings #-}
module Test.Expr
  ( tests
  )
  where

import Expr
import Types.Expr
import Types.Classes
import Types.Parser.Short
import qualified Types.Parser as P
import Parser( ShowMy, showMy )
import Types.Error
import Lib
--import Util

import Data.List.NonEmpty( NonEmpty )
import Data.Maybe( fromMaybe )
import Data.Void
import qualified Data.Map as M
import Control.Monad.Trans
import Control.Exception
import Test.HUnit
import Bound ( closed )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


parses :: P.Syntax -> IO (Ex Void)
parses = either
  (ioError . userError . displayException . MyExceptions)
  (return . fromMaybe (error "closed") . closed)
  . getCollect . resolve Nothing . expr
  
  
fails :: (NonEmpty ScopeError -> Assertion) -> P.Syntax -> Assertion
fails f = either f (assertFailure . show) . getCollect . resolve Nothing . expr
    

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
        e = (Var . Pub) (P.Ident "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env_ "private"
        e = Var (Priv "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env_ "var" #. "field"
        e = (Var (Priv "var")
          `At` Ident "field")
        in
        parses r >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r = self_ "obj" #. "path" #. "to" #. "value"
        e = ((((Var . Pub) (P.Ident "obj") 
          `At` Ident "path")
          `At` Ident "to")
          `At` Ident "value")
        in parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "rec assign public field" ~: let 
            r = block_ [ self_ "public" #= 1 ]
            e = (Block [] . M.fromList) [
              (Ident "public", (Closed . toRec) (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
       
        , "rec assign private field" ~: let
            r = block_ [ env_ "private" #= 1 ]
            e = (Block [(Closed . toRec) (Number 1)] (M.fromList []))
            in
            parses r >>= assertEqual (banner r) e
            
        , "tup assign public field" ~: let
            r = tup_ [ self_ "public" #= 1 ]
            e = (Block [] . M.fromList) [
              (Ident "public", (Closed . toRec) (Number 1))
              ]
            in parses r >>= assertEqual (banner r) e
          
        , "rec backwards reference" ~: let
            r = block_ [ env_ "one" #= 1, self_ "oneRef" #= env_ "one" ]
            e = (Block [(Closed . toRec) (Number 1)]
              . M.fromList) [
              (Ident "oneRef", (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "rec forwards reference" ~: let
            r = block_ [ self_ "twoRef" #= env_ "two", env_ "two" #= 2 ]
            e = (Block [(Closed . toRec) (Number 2)]
              . M.fromList) [
              (Ident "twoRef", (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "infinite reference" ~: let
            r = block_ [ env_ "selfRef" #= env_ "selfRef" ]
            e = (Block [(Closed . toRec . Var . F) (B 0)] (M.fromList []))
            in
            parses r >>= assertEqual (banner r) e
            
        , "reference to infinte loop" ~: let
            r = block_ [
              env_ "selfRef" #= env_ "selfRef",
              self_ "loop" #= env_ "selfRef"
              ]
            e = (Block [(Closed . toRec . Var . F) (B 0)] . M.fromList) [
              (Ident "loop",
                (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference in private definition" ~: let
            r = block_ [
              self_ "public" #= 1,
              env_ "notPublic" #= self_ "public"
              ]
            e = (Block [
              (Closed . toRec . Var . B) (Ident "public")
              ]. M.fromList) [
              (Ident "public", (Closed . toRec) (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r = block_ [
              self_ "public" #= 1,
              self_ "publicAgain" #= env_ "public"
              ]
            e = (Block []. M.fromList) [
              (Ident "public", (Closed . toRec) (Number 1)),
              (Ident "publicAgain",
                (Closed . toRec . Var . B) (Ident "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block_ [
              env_ "outer" #= 1,
              self_ "object" #= block_ [ self_ "refOuter" #= env_ "outer" ]
              ]
            e = (Block [(Closed . toRec) (Number 1)]
              . M.fromList) [
              (Ident "object",
                (Closed . toRec . Block [] . M.fromList) [
                  (Ident "refOuter",
                    (Closed . toRec . Var . F . F . F) (B 0))
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "reference global" ~: let
            r = block_ [
              self_ "here" #= 2,
              self_ "refMissing" #= env_ "global"
              ]
            e = (Block [] . M.fromList) [
              (Ident "here", (Closed . toRec) (Number 2)),
              (Ident "refMissing",
                (Closed . toRec . Var . F . F) (P.Priv "global"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r = block_ [
              self_ "b" #= self_ "a"
              ]
            e = (Block [] . M.fromList) [
              (Ident "b",
                (Closed . toRec . Var . B) (Ident "a"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "pun public assignment to introduce private reference" ~: let
            r = block_ [ self_ "b" ]
            e = Block [(Closed . toRec . Var . B) (Ident "b")] (M.fromList [])
            in parses r >>= assertEqual (banner r) e
            
            
        , "pun private assignment to introduce public reference enclosing private" ~: let
            r = block_ [ env_ "x" ]
            e = (Block [] . M.fromList) [
              (Ident "x",
                (Closed . toRec . Var . F . F) (P.Priv "x"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "assign to public path" ~: let
            r = block_ [ self_ "a" #. "field" #= 1 ]
            e = (Block [] . M.fromList) [
              (Ident "a", (Open . M.fromList) [
                (Ident "field", (Closed . toRec) (Number 1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning path" ~: let
            r = block_ [ self_ "a" #. "f" #= self_ "f" ]
            e = (Block [] . M.fromList) [
              (Ident "a", (Open . M.fromList) [
                (Ident "f",
                  (Closed . toRec . Var . B) (Ident "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning to long path" ~: let
            r = block_ [
              self_ "a" #. "f" #. "g" #=
                self_ "f" # block_ [ self_ "g" #= self_ "h" ]
              ]
            e = (Block [] . M.fromList) [
              (Ident "a", (Open . M.fromList) [
                (Ident "f", (Open . M.fromList) [
                  (Ident "g", (Closed . toRec)
                    ((Var . B) (Ident "f") `Update`
                      (Block [] . M.fromList) [
                        (Ident "g", (Closed . toRec) ((Var . B) (Ident "h")))
                        ]))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = block_ [ self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba" ]
            e = (Block [] . M.fromList) [
              (Ident "raba", 
                (Closed . toRec) ((((Var . F . F) (P.Priv "y1")
                    `At` Ident "a")
                    `At` Ident "ab")
                    `At` Ident "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r = block_ [
              env_ "y1" #= 1,
              self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba"
              ]
            e = (Block [(Closed . toRec) (Number 1)] . M.fromList) [
              (Ident "raba", (Closed . toRec) ((((Var . F) (B 0)
                  `At` Ident "a")
                  `At` Ident "ab")
                  `At` Ident "aba"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block_ [ self_ "a" #. "f" #= env_ "f" ]
            e = (Block [] . M.fromList) [
              (Ident "a", (Open . M.fromList) [
                (Ident "f",
                  (Closed . toRec . Var . F . F) (P.Priv "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = block_ [ env_ "var" #. "field" #= 2 ]
            e = Block [
              (Open . M.fromList) [
                (Ident "field",
                  (Closed . toRec) (Number 2))
                ]
              ] (M.fromList [])
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadow private variable" ~: let
            r = block_ [
              env_ "outer" #= 1,
              self_ "inner" #= block_ [
                env_ "outer" #= 2,
                self_ "shadow" #= env_ "outer"
                ]
              ]
            e = (Block [
              (Closed . toRec) (Number 1)
              ] . M.fromList) [
              (Ident "inner", (Closed . toRec . Block [
                (Closed . toRec) (Number 2)
                ] . M.fromList) [
                (Ident "shadow", (Closed . toRec . Var . F) (B 0))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "shadow public variable" ~: let
            r = block_ [
              self_ "outer" #= "hello",
              self_ "inner" #= block_ [
                self_ "shadow" #= env_ "outer",
                env_ "outer" #= "bye"
                ] #. "shadow"
              ]
            e = (Block [] . M.fromList) [
              (Ident "outer",
                (Closed . toRec) (String "hello")),
              (Ident "inner", (Closed . toRec) (((Block [
                (Closed . toRec) (String "bye")
                ] . M.fromList) [
                (Ident "shadow",
                  (Closed . toRec . Var . F) (B 0))
                ]) `At` Ident "shadow"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "shadowing update public using path" ~: let
            r = block_ [
              self_ "inner" #= block_ [
                self_ "var" #. "g" #= env_ "y"
                ]
              ]
            e = (Block [] . M.fromList) [
              (Ident "inner", (Closed . toRec . Block []
                . M.fromList) [
                (Ident "var", (Open . M.fromList) [
                  (Ident "g", (Closed . toRec . Var . F . F
                    . F . F) (P.Priv "y"))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadowing private using path ##todo implement" ~: let
            r = block_ [
              env_ "outer" #= block_ [ self_ "g" #= "hello" ],
              self_ "inner" #= block_ [ env_ "outer" #. "g" #= "bye" ]
              ]
            e = (Block [
              (Closed . toRec . Block [] . M.fromList) [
                (Ident "g", (Closed . toRec) (String "hello"))
                ]
              ] . M.fromList) [
              (Ident "inner", (Closed . toRec) (Block [
                (Closed . toRec) ((Var . F . F . F) (B 0) `Update` (Block [] . M.fromList) [
                  (Ident "g", (Closed . toRec) (String "bye"))
                  ])
                ] (M.fromList [])))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        ]
    
    , "update" ~: let
        r = env_ "x" # block_ [ self_ "b" #= env_ "y" ]
        e = Var (P.Priv "x") `Update` (Block [] . M.fromList) [
          (Ident "b", (Closed . toRec . Var . F . F) (P.Priv "y"))
          ]
        in
        parses r >>= assertEqual (banner r) e
        
    , "operation sugar" ~:
        [ "add" ~: let
            r = env_ "x" #+ env_ "y"
            e = ((Var (P.Priv "x") `At` Binop Add)  `Update`
              (Block [] . M.fromList) [
              (Ident "x", (Closed . toRec . Var . F . F) (P.Priv "y"))
              ]) `At` Ident "return"
            in
            parses r >>= assertEqual (banner r) e
          
        , "not" ~: let
            r = not_ (env_ "x")
            e = Var (P.Priv "x") `At` Unop Not
            in parses r >>= assertEqual (banner r) e
          
        ]
      
    , "destructuring" ~: let
        r = block_ [
          tup_ [
            self_ "a" #= self_ "oa",
            self_ "b" #= env_ "ob"
            ] #= env_ "o"
          ]
        e = (Block [
          (Closed . toRec) ((Var . F . F) (P.Priv "o") `At` Ident "b")
          ] . M.fromList) [
          (Ident "oa", (Closed . toRec)
            ((Var . F . F) (P.Priv "o") `At` Ident "a"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "destructuring unpack" ~: let
        r = block_ [
          self_ "ob" # tup_ [ self_ "a" #= env_ "oa" ] #= env_ "o"
          ]
        e = (Block [
          (Closed . toRec) ((Var . F . F) (P.Priv "o") `At` Ident "a")
          ] . M.fromList) [
          (Ident "ob", (Closed . toRec)
            ((Var . F . F) (P.Priv "o") `Fix` Ident "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring unpack with paths" ~: let
        r = block_ [
          self_ "rem" # tup_ [ self_ "f" #. "g" #= env_ "set" ] #= env_ "get"
          ]
        e = (Block [
          (Closed . toRec) (((Var . F . F) (P.Priv "get") `At` Ident "f") `At` Ident "g")
          ] . M.fromList) [
          (Ident "rem", (Closed . toRec)
            (((Var . F . F) (P.Priv "get") `Fix` Ident "f") `Fix` Ident "g"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "destructuring pun public" ~: let
        r = block_ [
          tup_ [ self_ "a" ] #= env_ "o"
          ]
        e = (Block [] . M.fromList) [
          (Ident "a",
            (Closed . toRec) ((Var . F . F) (P.Priv "o") `At` Ident "a"))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun private" ~: let
        r = block_ [
          tup_ [ env_ "a" ] #= env_ "o"
          ]
        e = Block [
          (Closed . toRec) ((Var . F . F) (P.Priv "o") `At` Ident "a")
          ] (M.fromList [])
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun path" ~: let
        r = block_ [
          tup_ [ env_ "a" #. "f" #. "g" ] #= self_ "f"
          ]
        e = Block [
          (Open . M.fromList) [
            (Ident "f", (Open . M.fromList) [
              (Ident "g", (Closed . toRec) ((((Var . B) (Ident "f")
                `At` Ident "a")
                `At` Ident "f")
                `At` Ident "g"))
              ])
            ]
          ] (M.fromList []) 
        in parses r >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r = block_ [
          tup_ [
            self_ "a" #. "aa" #= tup_ [ self_ "aaa" #= self_ "oaaa" ]
            ] #= env_ "o"
          ]
        e = (Block [] . M.fromList) [
          (Ident "oaaa", (Closed . toRec)
            ((((Var . F . F) (P.Priv "o")
              `At` Ident "a")
              `At` Ident "aa")
              `At` Ident "aaa"))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "enclosing scope binding" ~: let
        r = block_ [
          self_ "var" #= 1,
          env_ "enclosingVar" #= self_ "var",
          self_ "nested" #= block_ [
            self_ "var" #= 2,
            self_ "a" #= env_ "enclosingVar"
            ]
          ]
        e = (Block [
          (Closed . toRec . Var . B) (Ident "var")
          ] . M.fromList) [
          (Ident "var",
            (Closed . toRec) (Number 1)),
          (Ident "nested",
            (Closed . toRec . Block []
            . M.fromList) [
            (Ident "var",
              (Closed . toRec) (Number 2)),
            (Ident "a",
              (Closed . toRec . Var . F . F . F) (B 0))
            ])
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]
        