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
import Data.Functor.Identity (Identity)
import Control.Exception
import Test.HUnit


type Expr' k = Expr k Identity  
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


parses
  :: (Eq a, Show a)
  => Either [DefnError] (Expr' K (P.Name (Nec Ident) Key a))
  -> IO (Expr' K (P.Name (Nec Ident) Key a))
parses = either
  (ioError . userError . displayException
    . MyExceptions :: [DefnError] -> IO a)
  return
  
  
fails
  :: (Eq a, Show a)
  => ([DefnError] -> Assertion)
  -> Either [DefnError] (Expr' K (P.Name (Nec Ident) Key a))
  -> Assertion
fails f = either f
  (ioError . userError . shows "Unexpected: " . show)
  
  
tests
  :: (S.Expr a, Eq b, Show b)
  => (a -> Either [DefnError] (Expr' K (P.Name (Nec Ident) Key b)))
  -> Test
tests expr =
  test
    [ "number"  ~: let
        r :: Lit a => a
        r = 1
        e = (Expr . return . Prim) (Number 1)
        in parses (expr r) >>= assertEqual (banner r) e
           
    , "string" ~: let
        r :: Lit a => a
        r = "test"
        e = (Expr . return . Prim) (Text "test")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "public variable" ~: let
        r :: Self a => a
        r = self_ "public"
        e = (Expr . return . Var . P.In . P.Pub) (K_ "public")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "private variable" ~: let
        r :: Local a => a
        r = local_ "private"
        e = (Expr . return . Var . P.In . P.Priv) (Nec Req "private")
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "field access" ~: let
        r :: S.Expr a => a
        r = local_ "var" #. "field"
        e = (Expr . return)
          ((Expr . return . Var . P.In . P.Priv) (Nec Req "var")
          `At` Key (K_ "field"))
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "chained field access" ~: let
        r :: S.Expr a => a
        r = self_ "obj" #. "path" #. "to" #. "value"
        e = (Expr . return) 
          ((Expr . return) 
            ((Expr . return)
              ((Expr . return . Var . P.In . P.Pub) (K_ "obj") 
              `At` Key (K_ "path"))
            `At` Key (K_ "to"))
          `At` Key (K_ "value"))
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "block" ~: 
        [ "rec assign public field" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "public" #= 1 )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec . Expr . return . Prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
       
        , "rec assign private field" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "private" #= 1 )
            e = (Expr . return . Block . Defns S.empty [
              ("private", (toRec . Expr . return . Prim) (Number 1))
              ]) (M.fromList [])
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "tup assign public field" ~: let
            r :: S.Expr a => a
            r = tup_ ( self_ "public" #= 1 )
            e = (Expr . return . Block . Fields . M.fromList) [
              (Key (K_ "public"), (Closed . Expr . return . Prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "rec backwards reference" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "one" #= 1 #: self_ "oneRef" #= local_ "one" )
            e = (Expr . return . Block . Defns S.empty [
              ("one", (toRec . Expr . return . Prim) (Number 1))
              ] . M.fromList) [
              (Key (K_ "oneRef"), (Closed . toRec . Expr . return . Var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e

        , "rec forwards reference" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "twoRef" #= local_ "two" #: local_ "two" #= 2 )
            e = (Expr . return . Block . Defns S.empty [
              ("two", (toRec . Expr . return . Prim) (Number 2))
              ] . M.fromList) [
              (Key (K_ "twoRef"), (Closed . toRec . Expr . return . Var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "rec self reference" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "selfRef" #= local_ "selfRef" )
            e = (Expr . return . Block . Defns S.empty [
              ("selfRef", (toRec . Expr . return . Var . F) (B 0))
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
            e = [(OlappedSet . P.Pub . P.Pure) (K_ "x")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "cannot assign same public and private variable" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "a" #= "first" #: self_ "a" #= "second" )
            e = [OlappedVis "a"]
            in fails (assertEqual (banner r) e) (expr r)
            
            
        , "cannot assign variable twice in tup block" ~: let
            r :: S.Expr a => a
            r = tup_ ( self_ "ab" #= local_ "ab" #: self_ "ab" #= 2 )
            e = [(OlappedSet . P.Pub . P.Pure) (K_ "ab")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "reference to infinte loop" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "selfRef" #= local_ "selfRef"
              #: self_ "loop" #= local_ "selfRef"
              )
            e = (Expr . return . Block . Defns S.empty [
              ("selfRef", (toRec . Expr . return . Var . F) (B 0))
              ] . M.fromList) [
              (Key (K_ "loop"), (Closed . toRec . Expr . return . Var . F) (B 0))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "public reference in private definition" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "public" #= 1
              #: local_ "notPublic" #= self_ "public"
              )
            e = (Expr . return . Block . Defns S.empty [
              ("notPublic", (toRec . Expr . return . Var . B . Key) (K_ "public"))
              ] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec . Expr . return . Prim) (Number 1))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "private reference to public definition" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "public" #= 1
              #: self_ "publicAgain" #= local_ "public"
              )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "public"), (Closed . toRec . Expr . return . Prim) (Number 1)),
              (Key (K_ "publicAgain"), (Closed . toRec . Expr . return
                . Var . B . Key) (K_ "public"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested scope" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "outer" #= 1
              #: self_ "object" #= block_ ( self_ "refOuter" #= local_ "outer" )
              )
            e = (Expr . return . Block . Defns S.empty [
              ("outer", (toRec . Expr . return . Prim) (Number 1))
              ] . M.fromList) [
              (Key (K_ "object"), (Closed . toRec . Expr . return
                . Block . Defns S.empty [] . M.fromList) [
                  (Key (K_ "refOuter"), (Closed . toRec . Expr . return
                    . Var . F . F . F) (B 0))
                  ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "reference global" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "here" #= 2
              #: self_ "refMissing" #= local_ "global"
              )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "here"), (Closed . toRec . Expr . return . Prim) (Number  2)),
              (Key (K_ "refMissing"), (Closed . toRec . Expr . return
                . Var . F . F . P.In . P.Priv) (Nec Req "global"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "reference undeclared public field" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "b" #= self_ "a"
              )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "b"), (Closed . toRec . Expr . return . Var . B . Key) (K_ "a"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields scope to enclosing rec block" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "a" #= "str"
              #: self_ "b" #= tup_
                (  self_ "f" #= local_ "a" )
              )
            e = (Expr . return . Block . Defns S.empty [
              ("a", (toRec . Expr . return . Prim) (Text "str"))
              ] . M.fromList) [
              (Key (K_ "b"), (Closed . toRec . Expr . return
                . Block . Fields . M.fromList) [
                  (Key (K_ "f"), (Closed . Expr . return . Var . F) (B 0))
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
            e = (Expr . return . Block . Fields . M.fromList) [
              (Key (K_ "a"), (Closed . Expr . return . Prim) (Number  1)),
              (Key (K_ "b"), (Closed . Expr . return . Block . Fields . M.fromList) [
                (Key (K_ "f"), (Closed . Expr . return . Var . P.In . P.Pub) (K_ "a"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "nested tup fields not in private scope" ~: let
            r :: S.Expr a => a
            r = tup_
              ( self_ "b" #= tup_ ( self_ "bf" #= local_ "f" )
              #: self_ "f" #= local_ "g"
              )
            e = (Expr . return . Block . Fields . M.fromList) [
              (Key (K_ "b"), (Closed . Expr . return . Block . Fields . M.fromList) [
                (Key (K_ "bf"), (Closed . Expr . return . Var . P.In . P.Priv) (Nec Req "f"))
                ]),
              (Key (K_ "f"), (Closed . Expr . return . Var . P.In . P.Priv) (Nec Req "g"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "field declaration introduces private reference" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "b" #: self_ "x" #= local_ "b" )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "x"), (Closed . toRec . Expr . return . Var . B . Key) (K_ "b"))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
            
        , " tup public pun assigns outer declared public variable to local public field" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "b" #= tup_ ( self_ "b" ) )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "b"), (Closed . toRec . Expr . return . Block . Fields . M.fromList) [
                (Key (K_ "b"), (Closed . Expr . return . Var . B . Key) (K_ "b"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "tup private pun assigns declared variable in private scope to local public field" ~: let
            r :: S.Expr a => a
            r = tup_ ( local_ "x" )
            e = (Expr . return . Block . Fields . M.fromList) [
              (Key (K_ "x"), (Closed . Expr . return
                . Var . P.In . P.Priv) (Nec Req "x"))
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
            e = (Expr . return . Block . Defns S.empty [
              ("outer", (toRec . Expr . return . Prim) (Number  1))
              ] . M.fromList) [
              (Key (K_ "inner"), (Closed . toRec . Expr . return
                . Block . Defns S.empty [
                  ("outer", (toRec . Expr . return . Prim) (Number  2))
                  ] . M.fromList) [
                  (Key (K_ "shadow"), (Closed . toRec . Expr . return . Var . F) (B 0))
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
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "outer"), (Closed . toRec . Expr . return . Prim) (Text "hello")),
              (Key (K_ "inner"), (Closed . toRec . Expr . return)
                (((Expr . return . Block . Defns S.empty [
                  ("outer", (toRec . Expr . return . Prim) (Text "bye"))
                  ] . M.fromList) [
                  (Key (K_ "shadow"), (Closed . toRec . Expr . return . Var . F) (B 0))
                  ])
                `At` Key (K_ "shadow")))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
        ]
        
    , "paths" ~: 
        [ "assign to public path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "a" #. "field" #= 1 )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "field"), (Closed . toRec . Expr . return . Prim) (Number  1))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "public reference scopes to definition root when assigning path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "a" #. "f" #= self_ "f" )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "f"), (Closed . toRec . Expr . return
                  . Var . B . Key) (K_ "f"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "public reference scopes to definition root when assigning to long path" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "a" #. "f" #. "g" #=
                  self_ "f" # block_ ( self_ "g" #= self_ "h" )
              )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "f"), (Open . M.fromList) [
                  (Key (K_ "g"), (Closed . toRec . Expr . return)
                    ((Expr . return . Var . B . Key) (K_ "f")
                    `Update` (Defns S.empty [] . M.fromList) [
                      (Key (K_ "g"), (Closed . toRec . Expr . return
                        . Var . B . Key) (K_ "h"))
                      ]))
                  ])
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "assign chained access to long path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba" )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "raba"), (Closed . toRec . Expr . return)
                ((Expr . return)
                  ((Expr . return)
                    ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "y1")
                    `At` Key (K_ "a"))
                  `At` Key (K_ "ab"))
                `At` Key (K_ "aba")))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "substitution in assign chained access to long path" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "y1" #= 1
              #: self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba"
              )
            e = (Expr . return . Block . Defns S.empty [
              ("y1", (toRec . Expr . return . Prim) (Number  1))
              ] . M.fromList) [
              (Key (K_ "raba"), (Closed . toRec . Expr . return)
                ((Expr . return) 
                  ((Expr . return)
                    ((Expr . return . Var . F) (B 0)
                    `At` Key (K_ "a"))
                  `At` Key (K_ "ab"))
                `At` Key (K_ "aba")))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "private reference binding when assigning path" ~: let
            r :: S.Expr a => a
            r = block_ ( self_ "a" #. "f" #= local_ "f" )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "a"), (Open . M.fromList) [
                (Key (K_ "f"), (Closed . toRec . Expr . return
                  . Var . F . F . P.In . P.Priv) (Nec Req "f"))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
              
        , "assign private path" ~: let
            r :: S.Expr a => a
            r = block_ ( local_ "var" #. "field" #= 2 )
            e = (Expr . return . Block) (Defns S.empty [
              ("var", (toRec . Expr . return)
                ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Opt "var")
                `Update` (Fields . M.fromList) [
                  (Key (K_ "field"), (Closed . Expr . return . Prim) (Number  2))
                  ]))
              ] M.empty)
            in parses (expr r) >>= assertEqual (banner r) e
            
        , "assigning paths through already assigned value forbidden" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "x" #= tup_ ( self_ "a" #= 1 )
              #: self_ "x" #. "b" #= 2
              )
            e = [(OlappedSet . P.Pub . P.Pure) (K_ "x")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "assignment using distinct paths with shared prefix" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "x" #. "a" #= 1
              #: self_ "x" #. "b" #= 2
              )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "x"), (Open . M.fromList) [
                (Key (K_ "a"), (Closed . toRec . Expr . return . Prim) (Number  1)),
                (Key (K_ "b"), (Closed . toRec . Expr . return . Prim) (Number  2))
                ])
              ]
            in parses (expr r) >>= assertEqual (banner r) e
              
             
        , "assign to distinct parts of a private variable" ~: let
            r :: S.Expr a => a
            r = block_
              ( local_ "x" #. "y" #. "z" #= tup_ ( self_ "x" #= "hi" )
              #: local_ "x" #. "yy" #= tup_ ( self_ "abc" #= local_ "g" )
              )
            e = (Expr . return . Block) (Defns S.empty [
              ("x", (toRec . Expr . return)
                ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Opt "x")
                `Update` (Fields . M.fromList) [
                  (Key (K_ "y"), (Open . M.fromList) [
                    (Key (K_ "z"), (Closed . Expr . return . Block . Fields . M.fromList) [
                      (Key (K_ "x"), (Closed . Expr . return . Prim) (Text "hi"))
                      ])
                    ]),
                  (Key (K_ "yy"), (Closed . Expr . return . Block . Fields . M.fromList) [
                    (Key (K_ "abc"), (Closed . Expr . return
                      . Var . F . F . P.In . P.Priv) (Nec Req "g"))
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
            e = [(OlappedSet . P.Priv . P.Free) (P.Pure "x" `P.At` K_ "y")]
            in fails (assertEqual (banner r) e) (expr r)
            
        , "shadowing update public using path" ~: let
            r :: S.Expr a => a
            r = block_
              ( self_ "inner" #= block_
                ( self_ "var" #. "g" #= local_ "y"
                )
              )
            e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "inner"), (Closed . toRec . Expr . return
                . Block . Defns S.empty [] . M.fromList) [
                  (Key (K_ "var"), (Open . M.fromList) [
                    (Key (K_ "g"), (Closed . toRec . Expr . return . Var . F . F
                        . F . F . P.In . P.Priv) (Nec Req "y"))
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
            e = (Expr . return . Block . Defns S.empty [
              ("outer", (toRec . Expr . return . Block . Defns S.empty []
                . M.fromList) [
                  (Key (K_ "g"), (Closed . toRec . Expr . return . Prim) (Text "hello"))
                  ])
              ] . M.fromList) [
              (Key (K_ "inner"), (Closed . toRec . Expr . return . Block) (Defns S.empty [
                ("outer", (toRec . Expr . return)
                  ((Expr . return . Var . F . F . F) (B 0)
                  `Update` (Fields . M.fromList) [
                    (Key (K_ "g"), (Closed . Expr . return . Prim) (Text "bye"))
                    ]))
                ] M.empty))
              ]
            in parses (expr r) >>= assertEqual (banner r) e
        ]
    
    , "update" ~: let
        r :: S.Expr a => a
        r = local_ "x" # block_ ( self_ "b" #= local_ "y" )
        e = (Expr . return) 
          ((Expr . return . Var . P.In . P.Priv) (Nec Req "x")
          `Update` (Defns S.empty [] . M.fromList) [
            (Key (K_ "b"), (Closed . toRec . Expr . return
              . Var . F . F . P.In . P.Priv) (Nec Req "y"))
            ])
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "operation sugar" ~:
        [ "add" ~: let
            r :: (Lit a, Local a) => a
            r = local_ "x" #+ local_ "y"
            e = (Expr . return . Prim) (Binop Add
              ((Expr . return . Var . P.In . P.Priv) (Nec Req "x"))
              ((Expr . return . Var . P.In . P.Priv) (Nec Req "y")))
            in parses (expr r) >>= assertEqual (banner r) e
          
        , "not" ~: let
            r :: (Lit a, Local a) => a
            r = not_ (local_ "x")
            e = (Expr . return . Prim . Unop Not
              . Expr . return . Var . P.In . P.Priv) (Nec Req "x")
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
        e = (Expr . return . Block . Defns S.empty [
          ("ob", (toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key (K_ "b")))
          ] . M.fromList) [
          (Key (K_ "oa"), (Closed . toRec . Expr . return) 
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key (K_ "a")))
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
        e = [(OlappedMatch . P.Pure) (K_ "a")]
        in fails (assertEqual (banner r) e) (expr r)
    
    , "destructuring unpack" ~: let
        r :: S.Expr a => a
        r = block_
          ( self_ "ob" # tup_ ( self_ "a" #= local_ "oa" ) #= local_ "o"
          )
        e = (Expr . return . Block . Defns S.empty [
          ("oa", (toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "o") 
            `At` Key (K_ "a")))
          ] . M.fromList) [
          (Key (K_ "ob"), (Closed . toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "o")
            `Fix` Key (K_ "a")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring unpack with paths" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( self_ "rem" # tup_ ( self_ "f" #. "g" #= local_ "set" ) #= local_ "get"
          )
        e = (Expr . return . Block . Defns S.empty [
          ("set", (toRec . Expr . return)
            ((Expr . return)
              ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "get")
              `At` Key (K_ "f"))
            `At` Key (K_ "g")))
          ] . M.fromList) [
          (Key (K_ "rem"), (Closed . toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "get")
            `Fix` Key (K_ "f")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
        
    , "referencing destructured bindings" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( tup_  ( self_ "f" #= local_ "af" ) #= local_ "a"
          #: self_ "bf" #= local_ "af"
          )
        e = (Expr . return . Block . Defns S.empty [
          ("af", (toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "a")
            `At` Key (K_ "f")))
          ] . M.fromList) [
          (Key (K_ "bf"), (Closed . toRec . Expr . return . Var . F) (B 0))
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
        e = (Expr . return . Block) (Defns S.empty [
          ("a1", (toRec . Expr . return)
            ((Expr . return)
              ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "a")
              `At` Key (K_ "x"))
            `At` Key (K_ "y"))),
          ("a2", (toRec . Expr . return) 
            ((Expr . return)
              ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "a")
              `At` Key (K_ "x"))
            `At` Key (K_ "z")))
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
        e = [(OlappedMatch . P.Free) (P.Pure (K_ "x") `P.At` K_ "z")]
        in fails (assertEqual (banner r) e) (expr r)
    
    , "destructuring pun public" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( tup_ ( self_ "a" ) #= local_ "o"
          )
        e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
          (Key (K_ "a"), (Closed . toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key (K_ "a")))
          ]
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring pun private" ~: let
        r :: S.Expr a => a
        r = block_ 
          ( tup_ ( local_ "a" ) #= local_ "o"
          )
        e = (Expr . return . Block) (Defns S.empty [
          ("a", (toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "o")
            `At` Key (K_ "a")))
          ] M.empty)
        in parses (expr r) >>= assertEqual (banner r) e
        
    , "destructuring pun path" ~: let
        r :: S.Expr a => a
        r = block_
          ( tup_ ( local_ "a" #. "f" #. "g" ) #= self_ "f"
          )
        e = (Expr . return . Block) (Defns S.empty [
          ("a", (toRec . Expr . return)
            ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Opt "a")
            `Update` (Fields . M.fromList) [
              (Key (K_ "f"), (Open . M.fromList) [
                (Key (K_ "g"), (Closed . Expr . return)
                  ((Expr . return)
                    ((Expr . return)
                      ((Expr . return . Var . B . Key) (K_ "f")
                      `At` Key (K_ "a"))
                    `At` Key (K_ "f"))
                  `At` Key (K_ "g")))
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
        e = (Expr . return . Block . Defns S.empty [] . M.fromList) [
          (Key (K_ "oaaa"), (Closed . toRec . Expr . return)
            ((Expr . return)
              ((Expr . return) 
                ((Expr . return . Var . F . F . P.In . P.Priv) (Nec Req "o")
                  `At` Key (K_ "a"))
                `At` Key (K_ "aa"))
              `At` Key (K_ "aaa")))
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
        e = (Expr . return . Block . Defns S.empty [
          ("enclosingVar", 
            (toRec . Expr . return . Var . B . Key) (K_ "var"))
          ] . M.fromList) [
          (Key (K_ "var"),
            (Closed . toRec . Expr . return . Prim) (Number  1)),
          (Key (K_ "nested"),
            (Closed . toRec . Expr . return . Block . Defns S.empty [] . M.fromList) [
              (Key (K_ "var"),
                (Closed . toRec . Expr . return . Prim) (Number  2)),
              (Key (K_ "a"),
                (Closed . toRec . Expr . return . Var . F . F . F) (B 0))
              ])
          ]
        in parses (expr r) >>= assertEqual (banner r) e
    ]
        