{-# LANGUAGE OverloadedStrings, RankNTypes, FlexibleContexts, TypeFamilies #-}

module Repr
  ( tests
  )
  where

import My.Syntax.Parser (Printer, showP)
import My.Syntax.Repr (DefnError(..))
import qualified My.Types.Parser as P
import My.Types.Repr
import My.Syntax (K, MyException(..))
import My.Types.Syntax.Class
import Data.String (IsString)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Exception
import Test.HUnit
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


parses
  :: (Eq a, Show a)
  => Either [DefnError] (Repr K (P.Name (Nec Ident) P.Key a))
  -> IO (Repr K (P.Name (Nec Ident) P.Key a))
parses = either
  (ioError . userError . displayException
    . MyExceptions :: [DefnError] -> IO a)
  return
  
  
fails
  :: (Eq a, Show a)
  => ([DefnError] -> Assertion)
  -> Either [DefnError] (Repr K (P.Name (Nec Ident) P.Key a))
  -> Assertion
fails f = either f
  (ioError . userError . shows "Unexpected: " . show)
  
  
tests
  :: (Expr a, Eq b, Show b)
  => (a -> Either [DefnError] (Repr K (P.Name (Nec Ident) P.Key b)))
  -> Test
tests expr =
  test
    [ "number"  ~: let
        r :: Lit a => a
        r = 1
        e = Prim (Number 1)
        in parses (expr r) >>= assertEqual (banner r) e
           
    , "string" ~: let
        r :: Lit a => a
        r = "test"
        e = Prim (Text "test")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r :: Self a => a
        r = self_ "public"
        e = (Var . P.In . P.Pub) (P.K_ "public")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r :: Local a => a
        r = local_ "private"
        e = (Var . P.In . P.Priv) (Nec Req "private")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r :: Expr a => a
        r = local_ "Var" #. "field"
        e = (Var . P.In . P.Priv) (Nec Req "Var")
          `At` Key ("field")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r :: Expr a => a
        r = self_ "obj" #. "path" #. "to" #. "value"
        e = (((Var . P.In . P.Pub) (P.K_ "obj") 
          `At` Key ("path"))
          `At` Key ("to"))
          `At` Key ("value")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "Block" ~: 
        [ "rec assign public field" ~: let
            r :: Expr a => a
            r = block_ ( self_ "public" #= 1 )
            e = (Block . Defns [] . M.fromList) [
              (Key ("public"), (Closed . toRec . Prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
       
        , "rec assign private field" ~: let
            r :: Expr a => a
            r = block_ ( local_ "private" #= 1 )
            e = (Block . Defns [
              -- 0: "private"
              (toRec . Prim) (Number 1)
              ]) (M.fromList [])
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "tup assign public field" ~: let
            r :: Expr a => a
            r = tup_ ( self_ "public" #= 1 )
            e = (Block . Defns [] . M.fromList) [
              (Key "public", (Closed . toRec . Prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "rec backwards reference" ~: let
            r :: Expr a => a
            r = block_ ( local_ "one" #= 1 #: self_ "oneRef" #= local_ "one" )
            e = (Block . Defns [
              -- 0: "one"
              (toRec . Prim) (Number 1)
              ] . M.fromList) [
              (Key ("oneRef"), (Closed . toRec . Var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e

        , "rec forwards reference" ~: let
            r :: Expr a => a
            r = block_ ( self_ "twoRef" #= local_ "two" #: local_ "two" #= 2 )
            e = (Block . Defns [
              -- 0: "two"
              (toRec . Prim) (Number 2)
              ] . M.fromList) [
              (Key ("twoRef"), (Closed . toRec . Var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "rec self reference" ~: let
            r :: Expr a => a
            r = block_ ( local_ "selfRef" #= local_ "selfRef" )
            e = (Block . Defns [
              -- 0: "selfRef"
              (toRec . Var . F) (B 0)
              ] . M.fromList) []
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "cannot assign private variable twice" ~: let
            r :: Expr a => a
            r = block_ ( local_ "a" #= 1 #: local_ "a" #= "hello" )
            e = [(OlappedSet . P.Priv) (P.Pure "a")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "cannot assign public variable twice" ~: let
            r :: Expr a => a
            r = block_ ( self_ "x" #= 1 #: self_ "x" #= local_ "a" )
            e = [(OlappedSet . P.Pub . P.Pure) (P.K_ "x")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "cannot assign same public and private variable" ~: let
            r :: Expr a => a
            r = block_ ( local_ "a" #= "first" #: self_ "a" #= "second" )
            e = [OlappedVis "a"]
            in fails (assertEqual (banner r) e) (expr r)
            
            
        , "cannot assign variable twice in tup Block" ~: let
            r :: Expr a => a
            r = tup_ ( self_ "ab" #= local_ "ab" #: self_ "ab" #= 2 )
            e = [(OlappedSet . P.Pub . P.Pure) (P.K_ "ab")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "reference to infinte loop" ~: let
            r :: Expr a => a
            r = block_
              ( local_ "selfRef" #= local_ "selfRef"
              #: self_ "loop" #= local_ "selfRef"
              )
            e = (Block . Defns [
              -- 0: "selfRef"
              (toRec . Var . F) (B 0)
              ] . M.fromList) [
              (Key "loop", (Closed . toRec . Var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "public reference in private definition" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "public" #= 1
              #: local_ "notPublic" #= self_ "public"
              )
            e = (Block . Defns [
              -- 0: "notPublic"
              (toRec . Var . B . Key) ("public")
              ] . M.fromList) [
              (Key ("public"), (Closed . toRec . Prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "public" #= 1
              #: self_ "publicAgain" #= local_ "public"
              )
            e = (Block . Defns [] . M.fromList) [
              (Key ("public"), (Closed . toRec . Prim) (Number 1)),
              (Key ("publicAgain"), (Closed . toRec . Var . B . Key) ("public"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r :: Expr a => a
            r = block_
              ( local_ "outer" #= 1
              #: self_ "object" #= block_ ( self_ "refOuter" #= local_ "outer" )
              )
            e = (Block . Defns [
              -- 0: "outer"
              (toRec . Prim) (Number 1)
              ] . M.fromList) [
              (Key ("object"), (Closed . toRec . Block . Defns [] . M.fromList) [
                  (Key ("refOuter"), (Closed . toRec . Var . F . F . F) (B 0))
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "reference global" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "here" #= 2
              #: self_ "refMissing" #= local_ "global"
              )
            e = (Block . Defns [] . M.fromList) [
              (Key "here", (Closed . toRec . Prim) (Number  2)),
              (Key "refMissing", (Closed . toRec . Var
                . F . F . P.In . P.Priv) (Nec Req "global"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "b" #= self_ "a"
              )
            e = (Block . Defns [] . M.fromList) [
              (Key ("b"), (Closed . toRec . Var . B . Key) ("a"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields scope to enclosing rec Block" ~: let
            r :: Expr a => a
            r = block_
              ( local_ "a" #= "str"
              #: self_ "b" #= tup_
                (  self_ "f" #= local_ "a" )
              )
            e = (Block . Defns [
              -- 0: "a"
              (toRec . Prim) (Text "str")
              ] . M.fromList) [
              (Key "b", (Closed . toRec . Block . Defns [] . M.fromList) [
                  (Key "f", (Closed . toRec . Var . F . F . F) (B 0))
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields not publicly referable" ~: let
            r :: Expr a => a
            r = tup_
              ( self_ "a" #= 1
              #: self_ "b" #= tup_
                ( self_ "f" #= self_ "a" )
              )
            e = (Block . Defns [] . M.fromList) [
              (Key "a", (Closed . toRec . Prim) (Number  1)),
              (Key "b", (Closed . toRec . Block . Defns [] . M.fromList) [
                (Key "f", (Closed . toRec . Var
                  . F . F . F . F . P.In . P.Pub) (P.K_ "a"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields not in private scope" ~: let
            r :: Expr a => a
            r = tup_
              ( self_ "b" #= tup_ ( self_ "bf" #= local_ "f" )
              #: self_ "f" #= local_ "g"
              )
            e = (Block . Defns [] . M.fromList) [
              (Key "b", (Closed . toRec . Block . Defns [] . M.fromList) [
                (Key "bf", (Closed . toRec . Var
                  . F . F . F . F . P.In . P.Priv) (Nec Req "f"))
                ]),
              (Key "f", (Closed . toRec . Var
                . F . F . P.In . P.Priv) (Nec Req "g"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "field declaration introduces private reference" ~: let
            r :: Expr a => a
            r = block_ ( self_ "b" #: self_ "x" #= local_ "b" )
            e = (Block . Defns [] . M.fromList) [
              (Key "x", (Closed . toRec . Var . B) (Key "b"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
            
        , " tup public pun assigns outer declared public variable to local public field" ~: let
            r :: Expr a => a
            r = block_ ( self_ "b" #= tup_ ( self_ "b" ) )
            e = (Block . Defns [] . M.fromList) [
              (Key "b", (Closed . toRec . Block . Defns [] . M.fromList) [
                (Key "b", (Closed . toRec . Var . F . F . B . Key) ("b"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "tup private pun assigns declared variable in private scope to local public field" ~: let
            r :: Expr a => a
            r = tup_ ( local_ "x" )
            e = (Block . Defns [] . M.fromList) [
              (Key "x", (Closed . toRec . Var . F . F . P.In . P.Priv) (Nec Req "x"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
             
        , "shadow private variable" ~: let
            r :: Expr a => a
            r = block_
              ( local_ "outer" #= 1
              #: self_ "inner" #= block_
                ( local_ "outer" #= 2
                #: self_ "shadow" #= local_ "outer"
                )
              )
            e = (Block . Defns [
              -- 0: "outer"
              (toRec . Prim) (Number  1)
              ] . M.fromList) [
              (Key "inner", (Closed . toRec . Block . Defns [
                  -- 0: "outer"
                  (toRec . Prim) (Number  2)
                  ] . M.fromList) [
                  (Key "shadow", (Closed . toRec . Var . F) (B 0))
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "shadow public variable" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "outer" #= "hello"
              #: self_ "inner" #= block_
                ( self_ "shadow" #= local_ "outer"
                #: local_ "outer" #= "bye"
                ) #. "shadow"
              )
            e = (Block . Defns [] . M.fromList) [
              (Key "outer", (Closed . toRec . Prim) (Text "hello")),
              (Key "inner", (Closed . toRec)
                (((Block . Defns [
                  -- 0: "outer"
                  (toRec . Prim) (Text "bye")
                  ] . M.fromList) [
                  (Key "shadow", (Closed . toRec . Var . F) (B 0))
                  ])
                `At` Key "shadow"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
        ]
        
    , "paths" ~: 
        [ "assign to public path" ~: let
            r :: Expr a => a
            r = block_ ( self_ "a" #. "field" #= 1 )
            e = (Block . Defns [] . M.fromList) [
              (Key ("a"), (Open . M.fromList) [
                (Key ("field"), (Closed . toRec . Prim) (Number  1))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "public reference scopes to definition root when assigning path" ~: let
            r :: Expr a => a
            r = block_ ( self_ "a" #. "f" #= self_ "f" )
            e = (Block . Defns [] . M.fromList) [
              (Key ("a"), (Open . M.fromList) [
                (Key ("f"), (Closed . toRec . Var . B . Key) ("f"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning to long path" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "a" #. "f" #. "g" #=
                  self_ "f" # block_ ( self_ "g" #= self_ "h" )
              )
            e = (Block . Defns [] . M.fromList) [
              (Key "a", (Open . M.fromList) [
                (Key "f", (Open . M.fromList) [
                  (Key "g", (Closed . toRec)
                    ((Var . B) (Key "f")
                    `Update` (Defns [] . M.fromList) [
                      (Key "g", (Closed . toRec . Var . B) (Key "h"))
                      ]))
                  ])
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r :: Expr a => a
            r = block_ ( self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba" )
            e = (Block . Defns [] . M.fromList) [
              (Key "raba", (Closed . toRec)
                ((((Var . F . F . P.In . P.Priv) (Nec Req "y1")
                `At` Key "a")
                `At` Key "ab")
                `At` Key "aba"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r :: Expr a => a
            r = block_
              ( local_ "y1" #= 1
              #: self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba"
              )
            e = (Block . Defns [
              -- 0: "y1"
              (toRec . Prim) (Number  1)
              ] . M.fromList) [
              (Key "raba", (Closed . toRec)
                ((((Var . F) (B 0)
                `At` Key "a")
                `At` Key "ab")
                `At` Key "aba"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r :: Expr a => a
            r = block_ ( self_ "a" #. "f" #= local_ "f" )
            e = (Block . Defns [] . M.fromList) [
              (Key "a", (Open . M.fromList) [
                (Key "f", (Closed . toRec . Var
                  . F . F . P.In . P.Priv) (Nec Req "f"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r :: Expr a => a
            r = block_ ( local_ "Var" #. "field" #= 2 )
            e = Block (Defns [
              -- 0: "Var"
              toRec
                ((Var . F . F . P.In . P.Priv) (Nec Opt "Var")
                `Update` (Defns [] . M.fromList) [
                  (Key "field", (Closed . toRec . Prim) (Number  2))
                  ])
              ] M.empty)
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "assigning paths through already assigned value forbidden" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "x" #= tup_ ( self_ "a" #= 1 )
              #: self_ "x" #. "b" #= 2
              )
            e = [(OlappedSet . P.Pub . P.Pure) (P.K_ "x")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "assignment using distinct paths with shared prefix" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "x" #. "a" #= 1
              #: self_ "x" #. "b" #= 2
              )
            e = (Block . Defns [] . M.fromList) [
              (Key ("x"), (Open . M.fromList) [
                (Key ("a"), (Closed . toRec . Prim) (Number  1)),
                (Key ("b"), (Closed . toRec . Prim) (Number  2))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
              
             
        , "assign to distinct parts of a private variable" ~: let
            r :: Expr a => a
            r = block_
              ( local_ "x" #. "y" #. "z" #= tup_ ( self_ "x" #= "hi" )
              #: local_ "x" #. "yy" #= tup_ ( self_ "abc" #= local_ "g" )
              )
            e = Block (Defns [
              -- 0: "x"
              toRec
                ((Var . F . F . P.In . P.Priv) (Nec Opt "x")
                `Update` (Defns [] . M.fromList) [
                  (Key "y", (Open . M.fromList) [
                    (Key "z", (Closed . toRec . Block . Defns [] . M.fromList) [
                      (Key "x", (Closed . toRec . Prim) (Text "hi"))
                      ])
                    ]),
                  (Key "yy", (Closed . toRec . Block . Defns [] . M.fromList) [
                    (Key "abc", (Closed . toRec . Var
                      . F . F . F . F . F . F . P.In . P.Priv) (Nec Req "g"))
                    ])
                  ])
              ] M.empty)
            in parses (expr r) >>= assertEqual (banner r) e
             
        , "assigned paths must be disjoint" ~: let
            r :: Expr a => a
            r = block_ 
              ( local_ "x" #. "y" #. "z" #= tup_ ( self_ "x" #= "hi" )
              #: local_ "x" #. "y" #= tup_ ( self_ "abc" #= local_ "g" )
              )
            e = [(OlappedSet . P.Priv . P.Free) (P.Pure "x" `P.At` P.K_ "y")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "shadowing Update public using path" ~: let
            r :: Expr a => a
            r = block_
              ( self_ "inner" #= block_
                ( self_ "Var" #. "g" #= local_ "y"
                )
              )
            e = (Block . Defns [] . M.fromList) [
              (Key ("inner"), (Closed . toRec . Block
                . Defns [] . M.fromList) [
                  (Key ("Var"), (Open . M.fromList) [
                    (Key ("g"), (Closed . toRec . Var
                      . F . F . F . F . P.In . P.Priv) (Nec Req "y"))
                    ])
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "shadowing private using path" ~: let
            r :: Expr a => a
            r = block_
              ( local_ "outer" #= block_ ( self_ "g" #= "hello" )
              #: self_ "inner" #= block_ ( local_ "outer" #. "g" #= "bye" )
              )
            e = (Block . Defns [
              -- 0: "outer"
              (toRec . Block . Defns []
                . M.fromList) [
                  (Key "g", (Closed . toRec . Prim) (Text "hello"))
                  ]
              ] . M.fromList) [
              (Key "inner", (Closed . toRec . Block) (Defns [
                -- 0: "outer"
                toRec
                  ((Var . F . F . F) (B 0)
                  `Update` (Defns [] . M.fromList) [
                    (Key "g", (Closed . toRec . Prim) (Text "bye"))
                    ])
                ] M.empty))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
        ]
    
    , "Update" ~: let
        r :: Expr a => a
        r = local_ "x" # block_ ( self_ "b" #= local_ "y" )
        e = (Var . P.In . P.Priv) (Nec Req "x")
          `Update` (Defns [] . M.fromList) [
            (Key ("b"), (Closed . toRec . Var
              . F . F . P.In . P.Priv) (Nec Req "y"))
            ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "operation sugar" ~:
        [ "add" ~: let
            r :: (Lit a, Local a) => a
            r = local_ "x" #+ local_ "y"
            e = Prim (Binop Add
              ((Var . P.In . P.Priv) (Nec Req "x"))
              ((Var . P.In . P.Priv) (Nec Req "y")))
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "not" ~: let
            r :: (Lit a, Local a) => a
            r = not_ (local_ "x")
            e = (Prim . Unop Not
              . Var . P.In . P.Priv) (Nec Req "x")
            in parses (expr r) >>= assertEqual (banner r) e
          
        ]
      
    , "destructuring" ~: let
        r :: Expr a => a
        r = block_
          ( tup_
            ( self_ "a" #= self_ "oa"
            #: self_ "b" #= local_ "ob"
            ) #= local_ "o"
          )
        e = (Block . Defns [
          -- 0: "ob"
          toRec
            ((Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key "b")
          ] . M.fromList) [
          (Key "oa", (Closed . toRec) 
            ((Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key "a"))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "cannot destructure field twice" ~: let
        r :: Expr a => a
        r = block_ (
          tup_
            ( self_ "a" #= self_ "pa"
            #: self_ "a" #= self_ "pb"
            ) #= local_ "p"
          )
        e = [(OlappedMatch . P.Pure) (P.K_ "a")]
        in fails (assertEqual (banner r) e) (expr r)
    
    , "destructuring unpack" ~: let
        r :: Expr a => a
        r = block_
          ( self_ "ob" # tup_ ( self_ "a" #= local_ "oa" ) #= local_ "o"
          )
        e = (Block . Defns [
          -- 0: "oa"
          toRec
            ((Var . F . F . P.In . P.Priv) (Nec Req "o") 
            `At` Key ("a"))
          ] . M.fromList) [
          (Key ("ob"), (Closed . toRec)
            ((Var . F . F . P.In . P.Priv) (Nec Req "o")
            `Fix` Key ("a")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring unpack with paths" ~: let
        r :: Expr a => a
        r = block_ 
          ( self_ "rem" # tup_ ( self_ "f" #. "g" #= local_ "set" ) #= local_ "get"
          )
        e = (Block . Defns [
          -- 0: "set"
          toRec
            (((Var . F . F . P.In . P.Priv) (Nec Req "get")
            `At` Key ("f"))
            `At` Key ("g"))
          ] . M.fromList) [
          (Key "rem", (Closed . toRec)
            ((Var . F . F . P.In . P.Priv) (Nec Req "get")
            `Fix` Key "f"))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
        
    , "referencing destructured bindings" ~: let
        r :: Expr a => a
        r = block_ 
          ( tup_  ( self_ "f" #= local_ "af" ) #= local_ "a"
          #: self_ "bf" #= local_ "af"
          )
        e = (Block . Defns [
          -- 0: "af"
          toRec
            ((Var . F . F . P.In . P.Priv) (Nec Req "a")
            `At` Key "f")
          ] . M.fromList) [
          (Key "bf", (Closed . toRec . Var . F) (B 0))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring with disjoint paths" ~: let
        r :: Expr a => a
        r = block_ (
            tup_
              ( self_ "x" #. "y" #= local_ "a1"
              #: self_ "x" #. "z" #= local_ "a2"
              ) #= local_ "a"
          )
        e = Block (Defns [
          -- 0: "a1"
          toRec
            (((Var . F . F . P.In . P.Priv) (Nec Req "a")
            `At` Key ("x"))
            `At` Key ("y")),
          -- 1: "a2"
          toRec 
            (((Var . F . F . P.In . P.Priv) (Nec Req "a")
            `At` Key ("x"))
            `At` Key ("z"))
          ] M.empty)
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructured paths must be disjoint" ~: let
        r :: Expr a => a
        r = block_
          ( tup_
              ( self_ "x" #. "z" #. "y" #= local_ "b1"
              #: self_ "x" #. "z" #= local_ "b2"
              ) #= local_ "a"
          )
        e = [(OlappedMatch . P.Free) (P.Pure (P.K_ "x") `P.At` P.K_  "z")]
        in fails (assertEqual (banner r) e) (expr r)
    
    , "destructuring pun public" ~: let
        r :: Expr a => a
        r = block_ 
          ( tup_ ( self_ "a" ) #= local_ "o"
          )
        e = (Block . Defns [] . M.fromList) [
          (Key ("a"), (Closed . toRec)
            ((Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key ("a")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring pun private" ~: let
        r :: Expr a => a
        r = block_ 
          ( tup_ ( local_ "a" ) #= local_ "o"
          )
        e = Block (Defns [
          -- 0: "a"
          toRec
            ((Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key ("a"))
          ] M.empty)
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring pun path" ~: let
        r :: Expr a => a
        r = block_
          ( tup_ ( local_ "a" #. "f" #. "g" ) #= self_ "f"
          )
        e = Block (Defns [
          -- 0: "a"
          toRec
            ((Var . F . F . P.In . P.Priv) (Nec Opt "a")
            `Update` (Defns [] . M.fromList) [
              (Key "f", (Open . M.fromList) [
                (Key "g", (Closed . toRec)
                  ((((Var . F . F . B) (Key "f")
                  `At` Key "a")
                  `At` Key "f")
                  `At` Key "g"))
                ])
              ])
          ] M.empty)
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r :: Expr a => a
        r = block_ 
          ( tup_ 
            ( self_ "a" #. "aa" #= tup_ ( self_ "aaa" #= self_ "oaaa" )
            ) #= local_ "o"
          )
        e = (Block . Defns [] . M.fromList) [
          (Key ("oaaa"), (Closed . toRec)
            ((((Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key ("a"))
            `At` Key ("aa"))
            `At` Key ("aaa")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
    
    , "enclosing scope binding" ~: let
        r :: Expr a => a
        r = block_
          ( self_ "Var" #= 1
          #: local_ "enclosingVar" #= self_ "Var"
          #: self_ "nested" #= block_
            ( self_ "Var" #= 2
            #: self_ "a" #= local_ "enclosingVar"
            )
          )
        e = (Block . Defns [
          -- 0: "enclosingVar"
          (toRec . Var . B . Key) ("Var")
          ] . M.fromList) [
          (Key ("Var"), (Closed . toRec . Prim) (Number  1)),
          (Key ("nested"), (Closed . toRec . Block 
            . Defns [] . M.fromList) [
              (Key ("Var"), (Closed . toRec . Prim) (Number  2)),
              (Key ("a"), (Closed . toRec . Var . F . F . F) (B 0))
              ])
          ]
        in parses (expr r) >>= assertEqual (banner r) e
    ]
        