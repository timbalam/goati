{-# LANGUAGE OverloadedStrings, RankNTypes, FlexibleContexts, TypeFamilies #-}

module Expr
  ( tests
  )
  where

import My.Syntax.Parser (Printer, showP)
import My.Syntax.Expr (DefnError(..))
import qualified My.Types.Parser as P
import My.Types.Expr
import My.Syntax (K, MyException(..))
import My.Types.Syntax.Class hiding (Expr)
import qualified My.Types.Syntax.Class as S (Expr)
import Data.String (IsString)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Exception
import Test.HUnit
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


parses
  :: (Eq a, Show a)
  => Either [DefnError] (Expr K (P.Name (Nec Ident) P.Key a))
  -> IO (Expr K (P.Name (Nec Ident) P.Key a))
parses = either
  (ioError . userError . displayException
    . MyExceptions :: [DefnError] -> IO a)
  return
  
  
fails
  :: (Eq a, Show a)
  => ([DefnError] -> Assertion)
  -> Either [DefnError] (Expr K (P.Name (Nec Ident) P.Key a))
  -> Assertion
fails f = either f
  (ioError . userError . shows "Unexpected: " . show)
  
  
tests
  :: (S.Expr a, Eq b, Show b)
  => (a -> Either [DefnError] (Expr K (P.Name (Nec Ident) P.Key b)))
  -> Test
tests expr =
  test
    [ "number"  ~: let
        r :: Lit a => a
        r = 1
        e = prim (Number 1)
        in parses (expr r) >>= assertEqual (banner r) e
           
    , "string" ~: let
        r :: Lit a => a
        r = "test"
        e = prim (Text "test")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r :: Self a => a
        r = self_ "public"
        e = (var . P.In . P.Pub) (P.K_ "public")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r :: Local a => a
        r = local_ "private"
        e = (var . P.In . P.Priv) (Nec Req "private")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r :: S.Expr a => a
        r = local_ "var" #. "field"
        e = (var . P.In . P.Priv) (Nec Req "var")
          `at` Key ("field")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r :: S.Expr a => a
        r = self_ "obj" #. "path" #. "to" #. "value"
        e = (((var . P.In . P.Pub) (P.K_ "obj") 
          `at` Key ("path"))
          `at` Key ("to"))
          `at` Key ("value")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "rec assign public field" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "public" #= 1 )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("public"), (Closed . toRec . prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
       
        , "rec assign private field" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "private" #= 1 )
            e = (block . Defns S.empty [
              ("private", (toRec . prim) (Number 1))
              ]) (M.fromList [])
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "tup assign public field" ~: let
            r :: S.Expr a => a
            r = tup_ ( self_ "public" #= 1 )
            e = (block . Fields . M.fromList) [
              (Key ("public"), (Closed . prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "rec backwards reference" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "one" #= 1 #: self_ "oneRef" #= local_ "one" )
            e = (block . Defns S.empty [
              ("one", (toRec . prim) (Number 1))
              ] . M.fromList) [
              (Key ("oneRef"), (Closed . toRec . var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e

        , "rec forwards reference" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "twoRef" #= local_ "two" #: local_ "two" #= 2 )
            e = (block . Defns S.empty [
              ("two", (toRec . prim) (Number 2))
              ] . M.fromList) [
              (Key ("twoRef"), (Closed . toRec . var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "rec self reference" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "selfRef" #= local_ "selfRef" )
            e = (block . Defns S.empty [
              ("selfRef", (toRec . var . F) (B 0))
              ] . M.fromList) []
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "cannot assign private variable twice" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "a" #= 1 #: local_ "a" #= "hello" )
            e = [(OlappedSet . P.Priv) (P.Pure "a")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "cannot assign public variable twice" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "x" #= 1 #: self_ "x" #= local_ "a" )
            e = [(OlappedSet . P.Pub . P.Pure) (P.K_ "x")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "cannot assign same public and private variable" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "a" #= "first" #: self_ "a" #= "second" )
            e = [OlappedVis "a"]
            in fails (assertEqual (banner r) e) (expr r)
            
            
        , "cannot assign variable twice in tup block" ~: let
            r :: S.Expr a => a
            r = tup_ ( self_ "ab" #= local_ "ab" #: self_ "ab" #= 2 )
            e = [(OlappedSet . P.Pub . P.Pure) (P.K_ "ab")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "reference to infinte loop" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "selfRef" #= local_ "selfRef"
              #: self_ "loop" #= local_ "selfRef"
              )
            e = (block . Defns S.empty [
              ("selfRef", (toRec . var . F) (B 0))
              ] . M.fromList) [
              (Key ("loop"), (Closed . toRec . var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "public reference in private definition" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "public" #= 1
              #: local_ "notPublic" #= self_ "public"
              )
            e = (block . Defns S.empty [
              ("notPublic", (toRec . var . B . Key) ("public"))
              ] . M.fromList) [
              (Key ("public"), (Closed . toRec . prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "public" #= 1
              #: self_ "publicAgain" #= local_ "public"
              )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("public"), (Closed . toRec . prim) (Number 1)),
              (Key ("publicAgain"), (Closed . toRec . var . B . Key) ("public"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "outer" #= 1
              #: self_ "object" #= block_ ( self_ "refOuter" #= local_ "outer" )
              )
            e = (block . Defns S.empty [
              ("outer", (toRec . prim) (Number 1))
              ] . M.fromList) [
              (Key ("object"), (Closed . toRec . block
                . Defns S.empty [] . M.fromList) [
                  (Key ("refOuter"), (Closed . toRec . var . F . F . F) (B 0))
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "reference global" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "here" #= 2
              #: self_ "refMissing" #= local_ "global"
              )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("here"), (Closed . toRec . prim) (Number  2)),
              (Key ("refMissing"), (Closed . toRec . var
                . F . F . P.In . P.Priv) (Nec Req "global"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "b" #= self_ "a"
              )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("b"), (Closed . toRec . var . B . Key) ("a"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields scope to enclosing rec block" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "a" #= "str"
              #: self_ "b" #= tup_
                (  self_ "f" #= local_ "a" )
              )
            e = (block . Defns S.empty [
              ("a", (toRec . prim) (Text "str"))
              ] . M.fromList) [
              (Key ("b"), (Closed . toRec . block
                . Fields . M.fromList) [
                  (Key ("f"), (Closed . var . F) (B 0))
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields not publicly referable" ~: let
            r :: S.Expr a => a
            r = tup_
              ( self_ "a" #= 1
              #: self_ "b" #= tup_
                ( self_ "f" #= self_ "a" )
              )
            e = (block . Fields . M.fromList) [
              (Key ("a"), (Closed . prim) (Number  1)),
              (Key ("b"), (Closed . block . Fields . M.fromList) [
                (Key ("f"), (Closed . var . P.In . P.Pub) (P.K_ "a"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields not in private scope" ~: let
            r :: S.Expr a => a
            r = tup_
              ( self_ "b" #= tup_ ( self_ "bf" #= local_ "f" )
              #: self_ "f" #= local_ "g"
              )
            e = (block . Fields . M.fromList) [
              (Key ("b"), (Closed . block . Fields . M.fromList) [
                (Key ("bf"), (Closed . var . P.In . P.Priv) (Nec Req "f"))
                ]),
              (Key ("f"), (Closed . var . P.In . P.Priv) (Nec Req "g"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "field declaration introduces private reference" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "b" #: self_ "x" #= local_ "b" )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("x"), (Closed . toRec . var . B . Key) ("b"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
            
        , " tup public pun assigns outer declared public variable to local public field" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "b" #= tup_ ( self_ "b" ) )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("b"), (Closed . toRec . block . Fields . M.fromList) [
                (Key ("b"), (Closed . var . B . Key) ("b"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "tup private pun assigns declared variable in private scope to local public field" ~: let
            r :: S.Expr a => a
            r = tup_ ( local_ "x" )
            e = (block . Fields . M.fromList) [
              (Key ("x"), (Closed . var . P.In . P.Priv) (Nec Req "x"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
             
        , "shadow private variable" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "outer" #= 1
              #: self_ "inner" #= block_
                ( local_ "outer" #= 2
                #: self_ "shadow" #= local_ "outer"
                )
              )
            e = (block . Defns S.empty [
              ("outer", (toRec . prim) (Number  1))
              ] . M.fromList) [
              (Key ("inner"), (Closed . toRec . block . Defns S.empty [
                  ("outer", (toRec . prim) (Number  2))
                  ] . M.fromList) [
                  (Key ("shadow"), (Closed . toRec . var . F) (B 0))
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "shadow public variable" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "outer" #= "hello"
              #: self_ "inner" #= block_
                ( self_ "shadow" #= local_ "outer"
                #: local_ "outer" #= "bye"
                ) #. "shadow"
              )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("outer"), (Closed . toRec . prim) (Text "hello")),
              (Key ("inner"), (Closed . toRec)
                (((block . Defns S.empty [
                  ("outer", (toRec . prim) (Text "bye"))
                  ] . M.fromList) [
                  (Key ("shadow"), (Closed . toRec . var . F) (B 0))
                  ])
                `at` Key ("shadow")))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
        ]
        
    , "paths" ~: 
        [ "assign to public path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "a" #. "field" #= 1 )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("a"), (Open . M.fromList) [
                (Key ("field"), (Closed . toRec . prim) (Number  1))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "public reference scopes to definition root when assigning path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "a" #. "f" #= self_ "f" )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("a"), (Open . M.fromList) [
                (Key ("f"), (Closed . toRec . var . B . Key) ("f"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning to long path" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "a" #. "f" #. "g" #=
                  self_ "f" # block_ ( self_ "g" #= self_ "h" )
              )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("a"), (Open . M.fromList) [
                (Key ("f"), (Open . M.fromList) [
                  (Key ("g"), (Closed . toRec)
                    ((var . B . Key) ("f")
                    `update` (Defns S.empty [] . M.fromList) [
                      (Key ("g"), (Closed . toRec . var . B . Key) ("h"))
                      ]))
                  ])
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba" )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("raba"), (Closed . toRec)
                ((((var . F . F . P.In . P.Priv) (Nec Req "y1")
                `at` Key ("a"))
                `at` Key ("ab"))
                `at` Key ("aba")))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "y1" #= 1
              #: self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba"
              )
            e = (block . Defns S.empty [
              ("y1", (toRec . prim) (Number  1))
              ] . M.fromList) [
              (Key ("raba"), (Closed . toRec)
                ((((var . F) (B 0)
                `at` Key ("a"))
                `at` Key ("ab"))
                `at` Key ("aba")))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "a" #. "f" #= local_ "f" )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("a"), (Open . M.fromList) [
                (Key ("f"), (Closed . toRec . var
                  . F . F . P.In . P.Priv) (Nec Req "f"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "var" #. "field" #= 2 )
            e = block (Defns S.empty [
              ("var", toRec
                ((var . F . F . P.In . P.Priv) (Nec Opt "var")
                `update` (Fields . M.fromList) [
                  (Key ("field"), (Closed . prim) (Number  2))
                  ]))
              ] M.empty)
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "assigning paths through already assigned value forbidden" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "x" #= tup_ ( self_ "a" #= 1 )
              #: self_ "x" #. "b" #= 2
              )
            e = [(OlappedSet . P.Pub . P.Pure) (P.K_ "x")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "assignment using distinct paths with shared prefix" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "x" #. "a" #= 1
              #: self_ "x" #. "b" #= 2
              )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("x"), (Open . M.fromList) [
                (Key ("a"), (Closed . toRec . prim) (Number  1)),
                (Key ("b"), (Closed . toRec . prim) (Number  2))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
              
             
        , "assign to distinct parts of a private variable" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "x" #. "y" #. "z" #= tup_ ( self_ "x" #= "hi" )
              #: local_ "x" #. "yy" #= tup_ ( self_ "abc" #= local_ "g" )
              )
            e = block (Defns S.empty [
              ("x", toRec
                ((var . F . F . P.In . P.Priv) (Nec Opt "x")
                `update` (Fields . M.fromList) [
                  (Key ("y"), (Open . M.fromList) [
                    (Key ("z"), (Closed . block . Fields . M.fromList) [
                      (Key ("x"), (Closed . prim) (Text "hi"))
                      ])
                    ]),
                  (Key ("yy"), (Closed . block . Fields . M.fromList) [
                    (Key ("abc"), (Closed . var
                      . F . F . P.In . P.Priv) (Nec Req "g"))
                    ])
                  ]))
              ] M.empty)
            in parses (expr r) >>= assertEqual (banner r) e
             
        , "assigned paths must be disjoint" ~: let
            r :: S.Expr a => a
            r = block_ 
              ( local_ "x" #. "y" #. "z" #= tup_ ( self_ "x" #= "hi" )
              #: local_ "x" #. "y" #= tup_ ( self_ "abc" #= local_ "g" )
              )
            e = [(OlappedSet . P.Priv . P.Free) (P.Pure "x" `P.At` P.K_ "y")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "shadowing update public using path" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "inner" #= block_
                ( self_ "var" #. "g" #= local_ "y"
                )
              )
            e = (block . Defns S.empty [] . M.fromList) [
              (Key ("inner"), (Closed . toRec . block
                . Defns S.empty [] . M.fromList) [
                  (Key ("var"), (Open . M.fromList) [
                    (Key ("g"), (Closed . toRec . var
                      . F . F . F . F . P.In . P.Priv) (Nec Req "y"))
                    ])
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "shadowing private using path" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "outer" #= block_ ( self_ "g" #= "hello" )
              #: self_ "inner" #= block_ ( local_ "outer" #. "g" #= "bye" )
              )
            e = (block . Defns S.empty [
              ("outer", (toRec . block . Defns S.empty []
                . M.fromList) [
                  (Key ("g"), (Closed . toRec . prim) (Text "hello"))
                  ])
              ] . M.fromList) [
              (Key ("inner"), (Closed . toRec . block) (Defns S.empty [
                ("outer", toRec
                  ((var . F . F . F) (B 0)
                  `update` (Fields . M.fromList) [
                    (Key ("g"), (Closed . prim) (Text "bye"))
                    ]))
                ] M.empty))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
        ]
    
    , "update" ~: let
        r :: S.Expr a => a
        r = local_ "x" # block_ ( self_ "b" #= local_ "y" )
        e = (var . P.In . P.Priv) (Nec Req "x")
          `update` (Defns S.empty [] . M.fromList) [
            (Key ("b"), (Closed . toRec . var
              . F . F . P.In . P.Priv) (Nec Req "y"))
            ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "operation sugar" ~:
        [ "add" ~: let
            r :: (Lit a, Local a) => a
            r = local_ "x" #+ local_ "y"
            e = prim (Binop Add
              ((var . P.In . P.Priv) (Nec Req "x"))
              ((var . P.In . P.Priv) (Nec Req "y")))
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "not" ~: let
            r :: (Lit a, Local a) => a
            r = not_ (local_ "x")
            e = (prim . Unop Not
              . var . P.In . P.Priv) (Nec Req "x")
            in parses (expr r) >>= assertEqual (banner r) e
          
        ]
      
    , "destructuring" ~: let
        r :: S.Expr a => a
        r = block_
          ( tup_
            ( self_ "a" #= self_ "oa"
            #: self_ "b" #= local_ "ob"
            ) #= local_ "o"
          )
        e = (block . Defns S.empty [
          ("ob", toRec
            ((var . F . F . P.In . P.Priv) (Nec Req "o")
            `at` Key ("b")))
          ] . M.fromList) [
          (Key ("oa"), (Closed . toRec) 
            ((var . F . F . P.In . P.Priv) (Nec Req "o")
            `at` Key ("a")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "cannot destructure field twice" ~: let
        r :: S.Expr a => a
        r = block_ (
          tup_
            ( self_ "a" #= self_ "pa"
            #: self_ "a" #= self_ "pb"
            ) #= local_ "p"
          )
        e = [(OlappedMatch . P.Pure) (P.K_ "a")]
        in fails (assertEqual (banner r) e) (expr r)
    
    , "destructuring unpack" ~: let
        r :: S.Expr a => a
        r = block_
          ( self_ "ob" # tup_ ( self_ "a" #= local_ "oa" ) #= local_ "o"
          )
        e = (block . Defns S.empty [
          ("oa", toRec
            ((var . F . F . P.In . P.Priv) (Nec Req "o") 
            `at` Key ("a")))
          ] . M.fromList) [
          (Key ("ob"), (Closed . toRec)
            ((var . F . F . P.In . P.Priv) (Nec Req "o")
            `fix` Key ("a")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring unpack with paths" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( self_ "rem" # tup_ ( self_ "f" #. "g" #= local_ "set" ) #= local_ "get"
          )
        e = (block . Defns S.empty [
          ("set", toRec
            (((var . F . F . P.In . P.Priv) (Nec Req "get")
            `at` Key ("f"))
            `at` Key ("g")))
          ] . M.fromList) [
          (Key ("rem"), (Closed . toRec)
            ((var . F . F . P.In . P.Priv) (Nec Req "get")
            `fix` Key ("f")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
        
    , "referencing destructured bindings" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( tup_  ( self_ "f" #= local_ "af" ) #= local_ "a"
          #: self_ "bf" #= local_ "af"
          )
        e = (block . Defns S.empty [
          ("af", toRec
            ((var . F . F . P.In . P.Priv) (Nec Req "a")
            `at` Key ("f")))
          ] . M.fromList) [
          (Key ("bf"), (Closed . toRec . var . F) (B 0))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring with disjoint paths" ~: let
        r :: S.Expr a => a
        r = block_ (
            tup_
              ( self_ "x" #. "y" #= local_ "a1"
              #: self_ "x" #. "z" #= local_ "a2"
              ) #= local_ "a"
          )
        e = block (Defns S.empty [
          ("a1", toRec
            (((var . F . F . P.In . P.Priv) (Nec Req "a")
            `at` Key ("x"))
            `at` Key ("y"))),
          ("a2", toRec 
            (((var . F . F . P.In . P.Priv) (Nec Req "a")
            `at` Key ("x"))
            `at` Key ("z")))
          ] M.empty)
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructured paths must be disjoint" ~: let
        r :: S.Expr a => a
        r = block_
          ( tup_
              ( self_ "x" #. "z" #. "y" #= local_ "b1"
              #: self_ "x" #. "z" #= local_ "b2"
              ) #= local_ "a"
          )
        e = [(OlappedMatch . P.Free) (P.Pure (P.K_ "x") `P.At` P.K_  "z")]
        in fails (assertEqual (banner r) e) (expr r)
    
    , "destructuring pun public" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( tup_ ( self_ "a" ) #= local_ "o"
          )
        e = (block . Defns S.empty [] . M.fromList) [
          (Key ("a"), (Closed . toRec)
            ((var . F . F . P.In . P.Priv) (Nec Req "o")
            `at` Key ("a")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring pun private" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( tup_ ( local_ "a" ) #= local_ "o"
          )
        e = block (Defns S.empty [
          ("a", toRec
            ((var . F . F . P.In . P.Priv) (Nec Req "o")
            `at` Key ("a")))
          ] M.empty)
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring pun path" ~: let
        r :: S.Expr a => a
        r = block_
          ( tup_ ( local_ "a" #. "f" #. "g" ) #= self_ "f"
          )
        e = block (Defns S.empty [
          ("a", toRec
            ((var . F . F . P.In . P.Priv) (Nec Opt "a")
            `update` (Fields . M.fromList) [
              (Key ("f"), (Open . M.fromList) [
                (Key ("g"), Closed
                  ((((var . B . Key) ("f")
                  `at` Key ("a"))
                  `at` Key ("f"))
                  `at` Key ("g")))
                ])
              ]))
          ] M.empty)
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "nested destructuring" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( tup_ 
            ( self_ "a" #. "aa" #= tup_ ( self_ "aaa" #= self_ "oaaa" )
            ) #= local_ "o"
          )
        e = (block . Defns S.empty [] . M.fromList) [
          (Key ("oaaa"), (Closed . toRec)
            ((((var . F . F . P.In . P.Priv) (Nec Req "o")
            `at` Key ("a"))
            `at` Key ("aa"))
            `at` Key ("aaa")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
    
    , "enclosing scope binding" ~: let
        r :: S.Expr a => a
        r = block_
          ( self_ "var" #= 1
          #: local_ "enclosingVar" #= self_ "var"
          #: self_ "nested" #= block_
            ( self_ "var" #= 2
            #: self_ "a" #= local_ "enclosingVar"
            )
          )
        e = (block . Defns S.empty [
          ("enclosingVar", (toRec . var . B . Key) ("var"))
          ] . M.fromList) [
          (Key ("var"), (Closed . toRec . prim) (Number  1)),
          (Key ("nested"), (Closed . toRec . block 
            . Defns S.empty [] . M.fromList) [
              (Key ("var"), (Closed . toRec . prim) (Number  2)),
              (Key ("a"), (Closed . toRec . var . F . F . F) (B 0))
              ])
          ]
        in parses (expr r) >>= assertEqual (banner r) e
    ]
        