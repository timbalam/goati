{-# LANGUAGE OverloadedStrings #-}
module Test.Expr
  ( tests
  )
  where

import Expr
import Types.Expr
import Types.Parser.Short
import qualified Types.Parser as P
import Parser( ShowMy, showMy )
import Lib

import Data.Void
import qualified Data.Map as M
import Control.Exception
import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


parses
  :: P.Expr (P.Name Ident Key P.Import)
  -> IO (Expr K (P.Name (Nec Ident) Key P.Import))
parses = either
  (ioError . userError . displayException . MyExceptions :: [ScopeError] -> IO a)
  return
  . expr
  
  
fails
  :: ([ScopeError] -> Assertion)
  -> P.Expr (P.Name Ident Key P.Import) -> Assertion
fails f = either f
  (ioError . userError . shows "Unexpected: ". show)
  . expr
    

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
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "public")
              ] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec) (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
       
        , "rec assign private field" ~: let
            r = block_ [ env_ "private" #= 1 ]
            e = (Block . Defns [(Closed . toRec) (Number 1)]) (M.fromList [])
            in
            parses r >>= assertEqual (banner r) e
            
        , "tup assign public field" ~: let
            r = tup_ [ self_ "public" #= 1 ]
            e = (Block . Defns [] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec) (Number 1))
              ]
            in parses r >>= assertEqual (banner r) e
          
        , "rec backwards reference" ~: let
            r = block_ [ env_ "one" #= 1, self_ "oneRef" #= env_ "one" ]
            e = (Block . Defns [
              (Closed . toRec) (Number 1),
              (Closed . toRec . Var . B . Key) (K_ "oneRef")
              ]
              . M.fromList) [
              (Key (K_ "oneRef"), (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e

        , "rec forwards reference" ~: let
            r = block_ [ self_ "twoRef" #= env_ "two", env_ "two" #= 2 ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "twoRef"),
              (Closed . toRec) (Number 2)
              ]
              . M.fromList) [
              (Key (K_ "twoRef"), (Closed . toRec . Var . F) (B 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "rec self reference" ~: let
            r = block_ [ env_ "selfRef" #= env_ "selfRef" ]
            e = (Block . Defns [(Closed . toRec . Var . F) (B 0)]) (M.fromList [])
            in
            parses r >>= assertEqual (banner r) e
            
        , "cannot assign private variable twice ##todo scope error" ~: let
            r = block_ [ env_ "a" #= 1, env_ "a" #= "hello" ]
            in fails (assertFailure . show) r
            
        , "cannot assign public variable twice ##todo scope error" ~: let
            r = block_ [ self_ "x" #= 1, self_ "x" #= env_ "a" ]
            in fails (assertFailure . show) r
            
        , "cannot assign same public and private variable ##todo scope error" ~: let
            r = block_ [ env_ "a" #= "first", self_ "a" #= "second" ]
            in fails (assertFailure . show) r
            
            
        , "cannot assign variable twice in tup block ##todo scope error" ~: let
            r = tup_ [ self_ "ab" #= env_ "ab", self_ "ab" #= 2 ]
            in fails (assertFailure . show) r
            
        , "reference to infinte loop" ~: let
            r = block_ [
              env_ "selfRef" #= env_ "selfRef",
              self_ "loop" #= env_ "selfRef"
              ]
            e = (Block . Defns [
              (Closed . toRec . Var . F) (B 0),
              (Closed . toRec . Var . B . Key) (K_ "loop")
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
              (Closed . toRec . Var . B . Key) (K_ "public"),
              (Closed . toRec . Var . B . Key) (K_ "public")
              ]. M.fromList) [
              (Key (K_ "public"), (Closed . toRec) (Number 1))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r = block_ [
              self_ "public" #= 1,
              self_ "publicAgain" #= env_ "public"
              ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "public"),
              (Closed . toRec . Var . B . Key) (K_ "publicAgain")
              ]. M.fromList) [
              (Key (K_ "public"), (Closed . toRec) (Number 1)),
              (Key (K_ "publicAgain"), (Closed . toRec . Var . F) (B 0))
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r = block_ [
              env_ "outer" #= 1,
              self_ "object" #= block_ [ self_ "refOuter" #= env_ "outer" ]
              ]
            e = (Block . Defns [
              (Closed . toRec) (Number 1),
              (Closed . toRec . Var . B . Key) (K_ "object")
              ]
              . M.fromList) [
              (Key (K_ "object"),
                (Closed . toRec . Block . Defns [
                  (Closed . toRec . Var . B . Key) (K_ "refOuter")
                  ] . M.fromList) [
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
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "here"),
              (Closed . toRec . Var . B . Key) (K_ "refMissing")
              ] . M.fromList) [
              (Key (K_ "here"), (Closed . toRec) (Number 2)),
              (Key (K_ "refMissing"),
                (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "global"))
              ]
            in
            parses r >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r = block_ [
              self_ "b" #= self_ "a"
              ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "b")
              ] . M.fromList) [
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
              (Closed . toRec) (String "str"),
              (Closed . toRec . Var . B . Key) (K_ "b")
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
              (Key (K_ "a"), (Closed . toRec) (Number 1)),
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
            r = block_ [ self_ "b" ]
            e = Block (Defns [(Closed . toRec . Var . B . Key) (K_ "b")] M.empty)
            in parses r >>= assertEqual (banner r) e
            
            
        , " tup public pun assigns outer declared public variable to local public field" ~: let
            r = block_ [ self_ "b" #= tup_ [ self_ "b" ] ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "b")
              ] . M.fromList) [
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
              (Closed . toRec) (Number 1),
              (Closed . toRec . Var . B . Key) (K_ "inner")
              ] . M.fromList) [
              (Key (K_ "inner"), (Closed . toRec . Block . Defns [
                (Closed . toRec) (Number 2),
                (Closed . toRec . Var . B . Key) (K_ "shadow")
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
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "outer"),
              (Closed . toRec . Var . B . Key) (K_ "inner")
              ] . M.fromList) [
              (Key (K_ "outer"),
                (Closed . toRec) (String "hello")),
              (Key (K_ "inner"), (Closed . toRec) (((Block . Defns [
                (Closed . toRec . Var . B . Key) (K_ "shadow"),
                (Closed . toRec) (String "bye")
                ] . M.fromList) [
                (Key (K_ "shadow"),
                  (Closed . toRec . Var . F) (B 1))
                ]) `At` Key (K_ "shadow")))
              ]
            in parses r >>= assertEqual (banner r) e
        ]
        
      , "paths" ~: 
        [ "assign to public path" ~: let
            r = block_ [ self_ "a" #. "field" #= 1 ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "a")
              ] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "field"), (Closed . toRec) (Number 1))
                ])
              ]
            in parses r >>= assertEqual (banner r) e
          
        , "public reference scopes to definition root when assigning path" ~: let
            r = block_ [ self_ "a" #. "f" #= self_ "f" ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "a")
              ] . M.fromList) [
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
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "a")
              ] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "f"), (Open . M.fromList) [
                  (Key (K_ "g"), (Closed . toRec)
                    ((Var . B . Key) (K_ "f") `Update`
                      (Defns [
                        (Closed . toRec . Var . B . Key) (K_ "g")
                        ] . M.fromList) [
                        (Key (K_ "g"), (Closed . toRec . Var . B . Key) (K_ "h"))
                        ]))
                  ])
                ])
              ]
            in
            parses r >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r = block_ [ self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba" ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "raba")
              ] . M.fromList) [
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
              (Closed . toRec) (Number 1),
              (Closed . toRec . Var . B . Key) (K_ "raba")
              ] . M.fromList) [
              (Key (K_ "raba"), (Closed . toRec) ((((Var . F) (B 0)
                  `At` Key (K_ "a"))
                  `At` Key (K_ "ab"))
                  `At` Key (K_ "aba")))
              ]
            in parses r >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r = block_ [ self_ "a" #. "f" #= env_ "f" ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "a")
              ] . M.fromList) [
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
                (Key (K_ "field"), (Closed . toRec) (Number 2))
                ])
              ] M.empty)
            in
            parses r >>= assertEqual (banner r) e
            
        , "paths through already assigned value forbidden ##todo scope error" ~: let
          r = block_ [
            self_ "x" #= tup_ [ self_ "a" #= 1 ],
            self_ "x" #. "b" #= 2
            ]
          in fails (assertFailure . show) r
            
        , "assignment using distinct paths with shared prefix ##todo scope error" ~: let
            r = block_ [
              self_ "x" #. "a" #= 1,
              self_ "x" #. "b" #= 2
              ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "x")
              ] . M.fromList) [
              (Key (K_ "x"), (Open . M.fromList) [
                (Key (K_ "a"), (Closed . toRec) (Number 1)),
                (Key (K_ "b"), (Closed . toRec) (Number 2))
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
                        (Key (K_ "x"), (Closed . toRec) (String "hi"))
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
             
        , "cannot assign value along an assigned path ##todo scope error" ~: let
            r = block_ [
              env_ "x" #. "y" #. "z" #= tup_ [ self_ "x" #= "hi" ],
              env_ "x" #. "y" #= tup_ [ self_ "abc" #= env_ "g" ]
              ]
            in fails (assertFailure . show) r
            
        , "shadowing update public using path" ~: let
            r = block_ [
              self_ "inner" #= block_ [
                self_ "var" #. "g" #= env_ "y"
                ]
              ]
            e = (Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "inner")
              ] . M.fromList) [
              (Key (K_ "inner"),
                (Closed . toRec . Block . Defns [
                  (Closed . toRec . Var . B . Key) (K_ "var")
                  ] . M.fromList) [
                  (Key (K_ "var"), (Open . M.fromList) [
                    (Key (K_ "g"),
                      (Closed . toRec . Var . F . F
                        . F . F . P.In . P.Priv) (Nec Req "y"))
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
            e = (Block . Defns [
              (Closed . toRec . Block . Defns [
                (Closed . toRec . Var . B . Key) (K_ "g")
                ] . M.fromList) [
                (Key (K_ "g"), (Closed . toRec) (String "hello"))
                ],
              (Closed . toRec . Var . B . Key) (K_ "inner")
              ] . M.fromList) [
              (Key (K_ "inner"), (Closed . toRec . Block) (Defns [
                (Closed . toRec) ((Var . F . F . F) (B 0)
                  `Update` (Defns [] . M.fromList) [
                    (Key (K_ "g"), (Closed . toRec) (String "bye"))
                    ])
                ] M.empty))
              ]
            in
            parses r >>= assertEqual (banner r) e
        ]
    
    , "update" ~: let
        r = env_ "x" # block_ [ self_ "b" #= env_ "y" ]
        e = (Var . P.In . P.Priv) (Nec Req "x")
          `Update` (Defns [
            (Closed . toRec . Var . B . Key) (K_ "b")
            ] . M.fromList) [
            (Key (K_ "b"),
              (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "y"))
            ]
        in
        parses r >>= assertEqual (banner r) e
        
    , "operation sugar" ~:
        [ "add" ~: let
            r = env_ "x" #+ env_ "y"
            e = (((Var . P.In . P.Priv) (Nec Req "x") `At` Binop Add)  `Update`
              (Defns [] . M.fromList) [
                (Key (K_ "x"),
                  (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "y"))
                ]) `At` Key (K_ "return")
            in
            parses r >>= assertEqual (banner r) e
          
        , "not" ~: let
            r = not_ (env_ "x")
            e = (Var . P.In . P.Priv) (Nec Req "x") `At` Unop Not
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
          (Closed . toRec . Var . B . Key) (K_ "oa"),
          (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "o") `At` Key (K_ "b"))
          ] . M.fromList) [
          (Key (K_ "oa"), (Closed . toRec)
            ((Var . F . F . P.In . P.Priv) (Nec Req "o") `At` Key (K_ "a")))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "destructuring unpack" ~: let
        r = block_ [
          self_ "ob" # tup_ [ self_ "a" #= env_ "oa" ] #= env_ "o"
          ]
        e = (Block . Defns [
          (Closed . toRec . Var . B . Key) (K_ "ob"),
          (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "o") `At` Key (K_ "a"))
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
          (Closed . toRec . Var . B . Key) (K_ "rem"),
          (Closed . toRec) (((Var . F . F . P.In . P.Priv) (Nec Req "get") `At` Key (K_ "f")) `At` Key (K_ "g"))
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
          (Closed . toRec) ((Var . F . F . P.In . P.Priv) (Nec Req "a") `At` Key (K_ "f")),
          (Closed . toRec . Var . B . Key) (K_ "bf")
          ] . M.fromList) [
          (Key (K_ "bf"), (Closed . toRec . Var . F) (B 0))
          ]
        in parses r >>= assertEqual (banner r) e
    
    , "destructuring pun public" ~: let
        r = block_ [
          tup_ [ self_ "a" ] #= env_ "o"
          ]
        e = (Block . Defns [
          (Closed . toRec . Var . B . Key) (K_ "a")
          ] . M.fromList) [
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
        e = (Block . Defns [
          (Closed . toRec . Var . B . Key) (K_ "oaaa")
          ] . M.fromList) [
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
          (Closed . toRec . Var . B . Key) (K_ "var"),
          (Closed . toRec . Var . B . Key) (K_ "var"),
          (Closed . toRec . Var . B . Key) (K_ "nested")
          ] . M.fromList) [
          (Key (K_ "var"),
            (Closed . toRec) (Number 1)),
          (Key (K_ "nested"),
            (Closed . toRec . Block . Defns [
              (Closed . toRec . Var . B . Key) (K_ "var"),
              (Closed . toRec . Var . B . Key) (K_ "a")
              ] . M.fromList) [
              (Key (K_ "var"),
                (Closed . toRec) (Number 2)),
              (Key (K_ "a"),
                (Closed . toRec . Var . F . F . F) (B 1))
              ])
          ]
        in parses r >>= assertEqual (banner r) e
        
    ]
        