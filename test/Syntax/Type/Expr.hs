{-# LANGUAGE OverloadedStrings #-}

module Syntax.Type.Expr
  ( tests
  )
  where

import My.Expr
import My.Types.Expr
import My.Types.Parser.Short
import qualified My.Types.Parser as P
import My.Parser (ShowMy, showMy)
import qualified My
import Data.Void
import qualified Data.Map as M
import Control.Exception
import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


parses
  :: P.Expr (P.Name Ident Key P.Import)
  -> IO (Expr My.K (P.Name (Nec Ident) Key P.Import))
parses = either
  (ioError . userError . displayException
    . My.MyExceptions :: [DefnError] -> IO a)
  return
  . expr
  
  
fails
  :: ([DefnError] -> Assertion)
  -> P.Expr (P.Name Ident Key P.Import) -> Assertion
fails f = either f
  (ioError . userError . shows "Unexpected: ". show)
  . expr
    

tests =
  test
    [ "number"  ~: let
        r = 1
        e = Prim (Number 1)
        in
        parses r >>= assertEqual (banner r) e
           
    , "string" ~: let
        r = "test"
        e = Prim (String "test")
        in
        parses r >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r = self_ "public"
        e = (Var . P.In . P.Pub) (K_ "public")
        in
        parses r >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r = env_ "private"
        e = (Var . P.In . P.Priv) (Nec Req "private")
        in
        parses r >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r = env_ "var" #. "field"
        e = ((Var . P.In . P.Priv) (Nec Req "var")
          `At` Key (K_ "field"))
        in
        parses r >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r = self_ "obj" #. "path" #. "to" #. "value"
        e = ((((Var . P.In . P.Pub) (K_ "obj") 
          `At` Key (K_ "path"))
          `At` Key (K_ "to"))
          `At` Key (K_ "value"))
        in parses r >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "rec assign public field" ~: let 
            r = block_ [ self_ "public" #= 1 ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec. Prim) (Number   1))
              ]
            in
            parses r >>= assertEqual (banner r) e
       
        , "rec assign private field" ~: let
            r = block_ [ env_ "private" #= 1 ]
            e = (Block . Defns [(Closed . toRec. Prim) (Number   1)]) (M.fromList [])
            in
            parses r >>= assertEqual (banner r) e
            
        , "tup assign public field" ~: let
            r = tup_ [ self_ "public" #= 1 ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec. Prim) (Number   1))
              ]
            in parses r >>= assertEqual (banner r) e
          
        , "rec backwards reference" ~: let
            r = block_ [ env_ "one" #= 1, self_ "oneRef" #= env_ "one" ]
            e = (Block . Defns [
              (Closed . toRec . Prim) (Number   1)
              ]
              . M.fromList) [
              (Key (K_ "oneRef"), (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "rec forwards reference" ~: let
            r = block_ [ self_ "twoRef" #= env_ "two", env_ "two" #= 2 ]
            e = (Block . Defns [
              -- 0 : "two"
              (Closed . toRec . Prim) (Number   2)
              ]
              . M.fromList) [
              (Key (K_ "twoRef"), (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "rec self reference" ~: let
            r = block_ [ env_ "selfRef" #= env_ "selfRef" ]
            e = (Block . Defns [(Closed . toRec . Var . F) (B 0)]) (M.fromList [])
            in
            parses r >>= assertEqual (banner r) e
            
        , "cannot assign private variable twice" ~: let
            r = block_ [ env_ "a" #= 1, env_ "a" #= "hello" ]
            e = [(OlappedSet . P.Priv) (P.Pure "a")]
            in fails (assertEqual (banner r) e) r
            
        , "cannot assign public variable twice" ~: let
            r = block_ [ self_ "x" #= 1, self_ "x" #= env_ "a" ]
            e = [(OlappedSet . P.Pub . P.Pure) (K_ "x")]
            in fails (assertEqual (banner r) e) r
            
        , "cannot assign same public and private variable" ~: let
            r = block_ [ env_ "a" #= "first", self_ "a" #= "second" ]
            e = [OlappedVis "a"]
            in fails (assertEqual (banner r) e) r
            
            
        , "cannot assign variable twice in tup block" ~: let
            r = tup_ [ self_ "ab" #= env_ "ab", self_ "ab" #= 2 ]
            e = [(OlappedSet . P.Pub . P.Pure) (K_ "ab")]
            in fails (assertEqual (banner r) e) r
            
        , "reference to infinte loop" ~: let
            r = block_ [
              env_ "selfRef" #= env_ "selfRef",
              self_ "loop" #= env_ "selfRef"
              ]
            e = (Block . Defns [
              (Closed . toRec . Var . F) (B 0)
              ] . M.fromList) [
              (Key (K_ "loop"),
                (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference in private definition" ~: let
            r = block_ [
              self_ "public" #= 1,
              env_ "notP.Public" #= self_ "public"
              ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "public")
              ]. M.fromList) [
              (Key (K_ "public"), (Closed . toRec . Prim) (Number   1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r = block_ [
              self_ "public" #= 1,
              self_ "publicAgain" #= env_ "public"
              ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec . Prim) (Number   1)),
              (Key (K_ "publicAgain"),
                (Closed . toRec . Var . B . Key) (K_ "public"))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block_ [
              env_ "outer" #= 1,
              self_ "object" #= block_ [ self_ "refOuter" #= env_ "outer" ]
              ]
            e = (Block . Defns [
              -- 0 : "outer"
              (Closed . toRec . Prim) (Number   1)
              ]
              . M.fromList) [
              (Key (K_ "object"),
                (Closed . toRec . Block . Defns [] . M.fromList) [
                  (Key (K_ "refOuter"),
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
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "here"), (Closed . toRec . Prim) (Number  2)),
              (Key (K_ "refMissing"),
                (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "global"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r = block_ [
              self_ "b" #= self_ "a"
              ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "b"),
                (Closed . toRec . Var . B . Key) (K_ "a"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "nested tup fields scope to enclosing rec block" ~: let
            r = block_ [
              env_ "a" #= "str",
              self_ "b" #= tup_ [
                self_ "f" #= env_ "a"
                ]
              ]
            e = (Block . Defns [
              -- 0 : "a"
              (Closed . toRec . Prim) (String "str")
              ] . M.fromList) [
              (Key (K_ "b"),
                (Closed . toRec . Block . Defns [] . M.fromList) [
                  (Key (K_ "f"), (Closed . toRec . Var . F . F . F) (B 0))
                  ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "nested tup fields not publicly referencable" ~: let
            r = tup_ [
              self_ "a" #= 1,
              self_ "b" #= tup_ [
                self_ "f" #= self_ "a"
                ]
              ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "a"), (Closed . toRec . Prim) (Number  1)),
              (Key (K_ "b"), (Closed . toRec . Block . Defns [] . M.fromList) [
                (Key (K_ "f"),
                  (Closed . toRec . Var . F . F . F . F . P.In . P.Pub) (K_ "a"))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "nested tup fields not in private scope" ~: let
            r = tup_ [
              self_ "b" #= tup_ [ self_ "bf" #= env_ "f" ],
              self_ "f" #= env_ "g"
              ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "b"), (Closed . toRec . Block . Defns [] . M.fromList) [
                (Key (K_ "bf"),
                  (Closed . toRec . Var . F . F . F . F
                    . P.In . P.Priv) (Nec Req "f"))
                ]),
              (Key (K_ "f"),
                (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "g"))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "field declaration introduces private reference" ~: let
            r = block_ [ self_ "b", self_ "x" #= env_ "b" ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "x"), (Closed . toRec . Var . B . Key) (K_ "b"))
              ]
            in parses r >>= assertEqual (banner r) e
            
            
        , " tup public pun assigns outer declared public variable to local public field" ~: let
            r = block_ [ self_ "b" #= tup_ [ self_ "b" ] ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "b"), (Closed . toRec . Block . Defns [] . M.fromList) [
                (Key (K_ "b"), (Closed . toRec . Var . F . F . B . Key) (K_ "b"))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "tup private pun assigns declared variable in private scope to local public field" ~: let
            r = tup_ [ env_ "x" ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "x"),
                (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "x"))
              ]
            in parses r >>= assertEqual (banner r) e
             
        , "shadow private variable" ~: let
            r = block_ [
              env_ "outer" #= 1,
              self_ "inner" #= block_ [
                env_ "outer" #= 2,
                self_ "shadow" #= env_ "outer"
                ]
              ]
            e = (Block . Defns [
              -- 0 : "outer"
              (Closed . toRec . Prim) (Number  1)
              ] . M.fromList) [
              (Key (K_ "inner"), (Closed . toRec . Block . Defns [
                -- 0 : "outer"
                (Closed . toRec . Prim) (Number  2)
                ] . M.fromList) [
                (Key (K_ "shadow"), (Closed . toRec . Var . F) (B 0))
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
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "outer"),
                (Closed . toRec . Prim) (String "hello")),
              (Key (K_ "inner"), (Closed . toRec) (((Block . Defns [
                -- 0 : "outer"
                (Closed . toRec . Prim) (String "bye")
                ] . M.fromList) [
                (Key (K_ "shadow"),
                  (Closed . toRec . Var . F) (B 0))
                ]) `At` Key (K_ "shadow")))
              ]
            in parses r >>= assertEqual (banner r) e
        ]
        
      , "paths" ~: 
        [ "assign to public path" ~: let
            r = block_ [ self_ "a" #. "field" #= 1 ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "field"), (Closed . toRec . Prim) (Number  1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
          
        , "public reference scopes to definition root when assigning path" ~: let
            r = block_ [ self_ "a" #. "f" #= self_ "f" ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "f"),
                  (Closed . toRec . Var . B . Key) (K_ "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning to long path" ~: let
            r = block_ [
              self_ "a" #. "f" #. "g" #=
                self_ "f" # block_ [ self_ "g" #= self_ "h" ]
              ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "f"), (Open . M.fromList) [
                  (Key (K_ "g"), (Closed . toRec)
                    ((Var . B . Key) (K_ "f") `Update`
                      (Defns [] . M.fromList) [
                        (Key (K_ "g"), (Closed . toRec . Var . B . Key) (K_ "h"))
                        ]))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = block_ [ self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba" ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "raba"), 
                (Closed . toRec) ((((Var . F . F . P.In . P.Priv) (Nec Req "y1")
                  `At` Key (K_ "a"))
                  `At` Key (K_ "ab"))
                  `At` Key (K_ "aba")))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r = block_ [
              env_ "y1" #= 1,
              self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba"
              ]
            e = (Block . Defns [
              -- 0 : "y1"
              (Closed . toRec . Prim) (Number  1)
              ] . M.fromList) [
              (Key (K_ "raba"), (Closed . toRec) ((((Var . F) (B 0)
                  `At` Key (K_ "a"))
                  `At` Key (K_ "ab"))
                  `At` Key (K_ "aba")))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block_ [ self_ "a" #. "f" #= env_ "f" ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "f"),
                  (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "f"))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r = block_ [ env_ "var" #. "field" #= 2 ]
            e = Block (Defns [
              (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Opt "var")
                `Update` (Defns [] . M.fromList) [
                (Key (K_ "field"), (Closed . toRec . Prim) (Number  2))
                ])
              ] M.empty)
            in
            parses r >>= assertEqual (banner r) e
            
        , "assigning paths through already assigned value forbidden ##todo scope error" ~: let
          r = block_ [
            self_ "x" #= tup_ [ self_ "a" #= 1 ],
            self_ "x" #. "b" #= 2
            ]
          e = [(OlappedSet . P.Pub . P.Pure) (K_ "x")]
          in fails (assertEqual (banner r) e) r
            
        , "assignment using distinct paths with shared prefix ##todo scope error" ~: let
            r = block_ [
              self_ "x" #. "a" #= 1,
              self_ "x" #. "b" #= 2
              ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "x"), (Open . M.fromList) [
                (Key (K_ "a"), (Closed . toRec . Prim) (Number  1)),
                (Key (K_ "b"), (Closed . toRec . Prim) (Number  2))
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
              
             
        , "assign to distinct parts of a private variable" ~: let
            r = block_ [
              env_ "x" #. "y" #. "z" #= tup_ [ self_ "x" #= "hi" ],
              env_ "x" #. "yy" #= tup_ [ self_ "abc" #= env_ "g" ]
              ]
            e = Block (Defns [
              (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Opt "x")
                `Update` (Defns [] . M.fromList) [
                  (Key (K_ "y"), (Open . M.fromList) [
                    (Key (K_ "z"),
                      (Closed . toRec . Block . Defns [] . M.fromList) [
                        (Key (K_ "x"), (Closed . toRec . Prim) (String "hi"))
                        ])
                    ]),
                  (Key (K_ "yy"),
                    (Closed . toRec . Block . Defns [] . M.fromList) [
                      (Key (K_ "abc"),
                        (Closed . toRec . Var . F . F . F . F . F . F
                          . P.In . P.Priv) (Nec Req "g"))
                      ])
                  ])
              ] M.empty)
            in 
            parses r >>= assertEqual (banner r) e
             
        , "assigned paths must be disjoint" ~: let
            r = block_ [
              env_ "x" #. "y" #. "z" #= tup_ [ self_ "x" #= "hi" ],
              env_ "x" #. "y" #= tup_ [ self_ "abc" #= env_ "g" ]
              ]
            e = [(OlappedSet . P.Priv . P.Free) (P.Pure "x" `P.At` K_ "y")]
            in fails (assertEqual (banner r) e) r
            
        , "shadowing update public using path" ~: let
            r = block_ [
              self_ "inner" #= block_ [
                self_ "var" #. "g" #= env_ "y"
                ]
              ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "inner"),
                (Closed . toRec . Block . Defns [] . M.fromList) [
                  (Key (K_ "var"), (Open . M.fromList) [
                    (Key (K_ "g"),
                      (Closed . toRec . Var . F . F
                        . F . F . P.In . P.Priv) (Nec Req "y"))
                    ])
                  ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "shadowing private using path" ~: let
            r = block_ [
              env_ "outer" #= block_ [ self_ "g" #= "hello" ],
              self_ "inner" #= block_ [ env_ "outer" #. "g" #= "bye" ]
              ]
            e = (Block . Defns [
              -- 0 : "outer"
              (Closed . toRec . Block . Defns [] . M.fromList) [
                (Key (K_ "g"), (Closed . toRec . Prim) (String "hello"))
                ]
              ] . M.fromList) [
              (Key (K_ "inner"), (Closed . toRec . Block) (Defns [
                -- 0 : "outer"
                (Closed . toRec) ((Var . F . F . F) (B 0)
                  `Update` (Defns [] . M.fromList) [
                    (Key (K_ "g"), (Closed . toRec . Prim) (String "bye"))
                    ])
                ] M.empty))
              ]
            in
            parses r >>= assertEqual (banner r) e
        ]
    
    , "update" ~: let
        r = env_ "x" # block_ [ self_ "b" #= env_ "y" ]
        e = (Var . P.In . P.Priv) (Nec Req "x")
          `Update` (Defns [] . M.fromList) [
            (Key (K_ "b"),
              (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "y"))
            ]
        in
        parses r >>= assertEqual (banner r) e
        
    , "operation sugar" ~:
        [ "add" ~: let
            r = env_ "x" #+ env_ "y"
            e = Prim (Binop Add
              ((Var . P.In . P.Priv) (Nec Req "x"))
              ((Var . P.In . P.Priv) (Nec Req "y")))
            in
            parses r >>= assertEqual (banner r) e
          
        , "not" ~: let
            r = not_ (env_ "x")
            e = (Prim . Unop Not . Var . P.In . P.Priv) (Nec Req "x")
            in parses r >>= assertEqual (banner r) e
          
        ]
      
    , "destructuring" ~: let
        r = block_ [
          tup_ [
            self_ "a" #= self_ "oa",
            self_ "b" #= env_ "ob"
            ] #= env_ "o"
          ]
        e = (Block . Defns [
          -- 0 : "ob"
          (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key (K_ "b"))
          ] . M.fromList) [
          (Key (K_ "oa"),
            (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "o")
              `At` Key (K_ "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "cannot destructure field twice" ~: let
        r = block_ [
          tup_ [
            self_ "a" #= self_ "pa",
            self_ "a" #= self_ "pb"
            ] #= env_ "p"
          ]
        e = [(OlappedMatch . P.Pure) (K_ "a")]
        in fails (assertEqual (banner r) e) r
    
    , "destructuring unpack" ~: let
        r = block_ [
          self_ "ob" # tup_ [ self_ "a" #= env_ "oa" ] #= env_ "o"
          ]
        e = (Block . Defns [
          -- 0 : "oa"
          (Closed . toRec) ((Var . F . F . P.In
            . P.Priv) (Nec Req "o") 
            `At` Key (K_ "a"))
          ] . M.fromList) [
          (Key (K_ "ob"), (Closed . toRec)
            ((Var . F . F . P.In . P.Priv) (Nec Req "o") `Fix` Key (K_ "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring unpack with paths" ~: let
        r = block_ [
          self_ "rem" # tup_ [ self_ "f" #. "g" #= env_ "set" ] #= env_ "get"
          ]
        e = (Block . Defns [
          -- 0 : "set"
          (Closed . toRec) (((Var . F . F . P.In
            . P.Priv) (Nec Req "get")
            `At` Key (K_ "f"))
            `At` Key (K_ "g"))
          ] . M.fromList) [
          (Key (K_ "rem"), (Closed . toRec)
            ((Var . F . F . P.In . P.Priv) (Nec Req "get") `Fix` Key (K_ "f")))
          ]
        in parses r >>= assertEqual (banner r) e
        
        
    , "referencing destructured bindings" ~: let
        r = block_ [
          tup_  [ self_ "f" #= env_ "af" ] #= env_ "a",
          self_ "bf" #= env_ "af"
          ]
        e = (Block . Defns [
          -- 0 : "af"
          (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "a") `At` Key (K_ "f"))
          ] . M.fromList) [
          (Key (K_ "bf"), (Closed . toRec . Var . F) (B 0))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring with disjoint paths" ~: let
        r = block_ [
            tup_ [
              self_ "x" #. "y" #= env_ "a1",
              self_ "x" #. "z" #= env_ "a2"
              ] #= env_ "a"
          ]
        e = Block (Defns [
          -- 0 : "a1"
          (Closed . toRec) (((Var . F . F . P.In . P.Priv) (Nec Req "a")
            `At` Key (K_ "x"))
            `At` Key (K_ "y")),
          -- 1 : "a2"
          (Closed . toRec) (((Var . F . F . P.In . P.Priv) (Nec Req "a")
            `At` Key (K_ "x"))
            `At` Key (K_ "z"))
          ] M.empty)
        in parses r >>= assertEqual (banner r) e
        
    , "destructured paths must be disjoint" ~: let
        r = block_ [
            tup_ [
                self_ "x" #. "z" #. "y" #= env_ "b1",
                self_ "x" #. "z" #= env_ "b2"
            ] #= env_ "a"
          ]
        e = [(OlappedMatch . P.Free) (P.Pure (K_ "x") `P.At` K_ "z")]
        in fails (assertEqual (banner r) e) r
    
    , "destructuring pun public" ~: let
        r = block_ [
          tup_ [ self_ "a" ] #= env_ "o"
          ]
        e = (Block . Defns [] . M.fromList) [
          (Key (K_ "a"),
            (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "o") `At` Key (K_ "a")))
          ]
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun private" ~: let
        r = block_ [
          tup_ [ env_ "a" ] #= env_ "o"
          ]
        e = Block (Defns [
          (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "o") `At` Key (K_ "a"))
          ] M.empty)
        in parses r >>= assertEqual (banner r) e
        
    , "destructuring pun path" ~: let
        r = block_ [
          tup_ [ env_ "a" #. "f" #. "g" ] #= self_ "f"
          ]
        e = Block (Defns [
          (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Opt "a")
            `Update` (Defns [] . M.fromList) [
              (Key (K_ "f"), (Open . M.fromList) [
                (Key (K_ "g"), (Closed . toRec) ((((Var . F . F . B . Key) (K_ "f")
                  `At` Key (K_ "a"))
                  `At` Key (K_ "f"))
                  `At` Key (K_ "g")))
                ])
              ])
          ] M.empty)
        in parses r >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r = block_ [
          tup_ [
            self_ "a" #. "aa" #= tup_ [ self_ "aaa" #= self_ "oaaa" ]
            ] #= env_ "o"
          ]
        e = (Block . Defns [] . M.fromList) [
          (Key (K_ "oaaa"), (Closed . toRec)
            ((((Var . F . F . P.In . P.Priv) (Nec Req "o")
              `At` Key (K_ "a"))
              `At` Key (K_ "aa"))
              `At` Key (K_ "aaa")))
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
        e = (Block . Defns [
          (Closed . toRec . Var . B . Key) (K_ "var") -- 0: "enclosingVar"
          ] . M.fromList) [
          (Key (K_ "var"),
            (Closed . toRec . Prim) (Number  1)),
          (Key (K_ "nested"),
            (Closed . toRec . Block . Defns [] . M.fromList) [
              (Key (K_ "var"),
                (Closed . toRec . Prim) (Number  2)),
              (Key (K_ "a"),
                (Closed . toRec . Var . F . F . F) (B 0))
              ])
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]
        