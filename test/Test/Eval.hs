{-# LANGUAGE OverloadedStrings #-}
module Test.Eval
  ( tests
  )
  where

import Expr
import Eval
import Types.Expr
import Types.Classes
import Types.Parser.Short
import qualified Types.Parser as Parser
import Types.Error

import Data.List.NonEmpty( NonEmpty )
import Data.Foldable( asum )
import qualified Data.Map as M
import Control.Monad( (>=>) )
import Test.HUnit hiding ( Label )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: ShowMy a => Expr (Sym a) -> IO (Expr (Sym a))
run =
  either throwList return . closed
  >=> either throwMy return . eval
    
    
unclosed :: (NonEmpty (ScopeError Vid) -> Assertion) -> Expr (Sym Vid) -> Assertion
unclosed f =
  either f (ioError . userError . show :: Expr (Sym Vid) -> IO ())
  . closed


fails :: Show a => (EvalError Id -> Assertion) -> Expr a -> Assertion
fails f =
  either f (ioError . userError . show)
  . eval
  
  
parses :: Parser.Syntax -> IO (Expr (Sym Vid))
parses = either throwList return . expr


tests =
  test
    [ "add" ~: let
        r = (1 #+ 1)
        e = Number 2
        in
        parses r >>= run >>= assertEqual (banner r) e
          
    , "subtract" ~: let
        r = (1 #- 2)
        e = Number (-1)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "public variable" ~: let
        r = (Parser.Block [ self_ "pub" #= 1 ] #. "pub")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
       
    , "private variable" ~: let
        r = (Parser.Block [ env_ "priv" #= 1 ] #. "priv")
        in
        parses r >>= (fails . assertEqual "No field: priv" . LookupFailed) (Label "priv")
    
    , "private variable access backward" ~: let
        r = (Parser.Block [
          env_ "priv" #= 1,
          self_ "pub" #= env_ "priv"
          ] #. "pub")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "private variable access forward" ~: let
        r = (Parser.Block [
          self_ "pub" #= env_ "priv",
          env_ "priv" #= 1
          ] #. "pub")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access of public variable" ~: let
        r = (Parser.Block [
          self_ "a" #= 1,
          self_ "b" #= env_ "a"
          ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access in nested scope of public variable" ~: let
        r = (Parser.Block [
          self_ "a" #= 1,
          env_ "object" #= Parser.Block [ self_ "b" #= env_ "a" ],
          self_ "c" #= env_ "object" #. "b"
          ] #. "c")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access backward public variable from same scope" ~: let
        r = (Parser.Block [
          self_ "b" #= 2,
          self_ "a" #= self_ "b"
          ] #. "a")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access forward public variable from same scope" ~: let
        r = (Parser.Block [
          self_ "a" #= self_ "b",
          self_ "b" #= 2
          ] #. "a")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "nested public access" ~: let
        r = (Parser.Block [
          self_ "return" #=
            Parser.Block [ self_ "return" #= "str" ] #. "return"
          ] #. "return")
        e = String "str"
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "unbound variable" ~: let
        r = (Parser.Block [
          self_ "a" #= 2,
          self_ "b" #= env_ "c"
          ] #. "b")
        in
        parses r >>= (unclosed . assertEqual "Unbound var: c" . pure . ParamFree) (Priv "c")
          
    , "undefined variable" ~: let
        r = Parser.Block [
          self_ "b" #= self_ "a"
          ]
        in do
        let
          r1 = r #. "b"
          e1 = (ParamUndefined . Pub) (Label "a")
        parses r1 >>= fails (assertEqual ""  e1)
    
    , "application  overriding public variable" ~: let
        r = (Parser.Block [
          self_ "a" #= 2,
          self_ "b" #= self_ "a"
          ] # [ self_ "a" #= 1 ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "default definition forward" ~: let
        r = (Parser.Block [
          self_ "a" #= self_ "b",
          self_ "b" #= self_ "a"
          ] # [ self_ "b" #= 2 ] #. "a")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "default definition backward" ~: let
        r = (Parser.Block [
          self_ "a" #= self_ "b",
          self_ "b" #= self_ "a"
          ] # [ self_ "a" #= 1 ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
         
    , "route getter" ~: let
        r = (Parser.Block [
          self_ "a" #= Parser.Block [ self_ "aa" #= 2 ]
          ] #. "a" #. "aa")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "route setter" ~: let
        r = (Parser.Block [ self_ "a" #. "aa" #= 2 ] #. "a" #. "aa")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
    
    , "application overriding nested property" ~: let
        r = (Parser.Block [
          self_ "a" #= Parser.Block [ self_ "aa" #= 0 ],
          self_ "b" #= self_ "a" #. "aa"
          ] # [ self_ "a" #. "aa" #= 1 ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
     
    , "shadowing update" ~: let
        r = Parser.Block [
          env_ "x" #= Parser.Block [
            self_ "a" #= 1
            ],
          self_ "y" #= Parser.Block [
            env_ "x" #. "b" #= 2,
            self_ "return" #= env_ "x"
            ] #. "return"
          ] #. "y"
        in do
        let
          r1 = r #."a"
          e1 = Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "b"
          e2 = Number 2
        parses r2 >>= run >>= assertEqual (banner r2) e2
    
    , "original value is not affected by shadowing" ~: let
        r = (Parser.Block [
          env_ "x" #= Parser.Block [
            self_ "a" #= 2,
            self_ "b" #= 1
            ],
          self_ "x2" #= Parser.Block [
            env_ "x" #. "b" #= 2,
            self_ "return" #= env_ "x"
            ] #. "return",
          self_ "x1" #= env_ "x"
          ])
        in do
        let
          r1 = r #. "x1" #. "b"
          e1 = Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "x2" #. "b"
          e2 = Number 2
        parses r2 >>= run >>= assertEqual (banner r2) e2
          
    , "destructuring" ~: let
        r = (Parser.Block [
          env_ "obj" #= Parser.Block [
            self_ "a" #= 2,
            self_ "b" #= 3
            ],
          Parser.SetBlock [
            self_ "a" #= self_ "da",
            self_ "b" #= self_ "db"
            ] #= env_ "obj"
          ])
        in do
        let
          r1 = r #. "da"
          e1 = Number 2
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let 
          r2 = r #. "db"
          e2 = Number 3
        parses r2 >>= run >>= assertEqual (banner r2) e2
            
    , "destructuring unpack" ~: let
        r = (Parser.Block [
          env_ "obj" #= Parser.Block [
            self_ "a" #= 2,
            self_ "b" #= 3
            ],
          self_ "d" # [] #= env_ "obj"
          ] #. "d" #. "b")
        e = Number 3
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "nested destructuring" ~: let
        r = (Parser.Block [
          env_ "y1" #= Parser.Block [
            self_ "a" #= Parser.Block [
              self_ "aa" #= 3,
              self_ "ab" #= Parser.Block [ self_ "aba" #= 4 ]
              ]
            ],
          Parser.SetBlock [
            self_ "a" #. "aa" #= self_ "da",
            self_ "a" #. "ab" #. "aba" #= self_ "daba"
            ] #= env_ "y1",
          self_ "raba" #= env_ "y1" #. "a" #. "ab" #. "aba"
          ])
        in do
        let
          r1 = r #. "raba"
          e1 = Number 4
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "daba"
          e2 = Number 4
        parses r2 >>= run >>= assertEqual (banner r2) e2
      
    , "self references valid in extensions to an object" ~: let
        r = Parser.Block [
          env_ "w1" #= Parser.Block [ self_ "a" #= 1 ],
          self_ "w2" #= env_ "w1" # [ self_ "b" #= self_ "a" ],
          self_ "w3" #= self_ "w2" #. "a"
          ]
        in do
        let
          r1 = r #. "w2" #. "b"
          e1 = Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "w3"
          e2 = Number 1
        parses r2 >>= run >>= assertEqual (banner r2) e2
        
    , "object fields not in private scope for extensions to an object" ~: let
        r = (Parser.Block [
          env_ "a" #= 2,
          env_ "w1" #= Parser.Block [ self_ "a" #= 1 ],
          self_ "w2" #= env_ "w1" # [ self_ "b" #= env_ "a" ]
          ] #. "w2" #. "b")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access extension field of extended object" ~: let
        r = Parser.Block [
          self_ "w1" #= Parser.Block [ self_ "a" #= 1 ],
          self_ "w2" #= self_ "w1" # [ self_ "b" #= 2 ]
          ] #. "w2" #. "b"
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
            
    , "parent scope binding" ~: let
        r = (Parser.Block [
          self_ "inner" #= 1,
          env_ "parInner" #= self_ "inner",
          self_ "outer" #= Parser.Block [
            self_ "inner" #= 2,
            self_ "a" #= env_ "parInner"
            ]       
          ] #. "outer" #. "a")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "extension scope binding" ~: let
        r = (Parser.Block [
          env_ "inner" #= Parser.Block [
            env_ "var" #= 1,
            self_ "innerVar" #= env_ "var"
            ],
          env_ "outer" #= env_ "inner" #
            [ env_ "var" #= 2 ],
          self_ "a" #= env_ "outer" #. "innerVar"
          ] #. "a")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "self referencing definition" ~: let
        r = (Parser.Block [
          env_ "y" #= Parser.Block [
            self_ "a" #= env_ "y" #. "b",
            self_ "b" #= 1
            ],
          self_ "z" #= env_ "y" #. "a"
          ] #. "z")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
    
{-    
    , "application to referenced outer scope" ~: let
        r = (Parser.Block [
          env_ "y" #= Parser.Block [
            self_ "a" #= 1,
            env_ "b" #= 2,
            self_ "x" #= Parser.Block [ self_ "a" #= env_ "b" ]
            ],
          self_ "a" #= env_ "y" # (env_ "y" #. "x") #. "a"
          ] #. "a")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "application to nested object" ~: let
        r = (Parser.Block [
          env_ "y" #= Parser.Block [
            self_ "a" #= 1,
            self_ "x" #= Parser.Block [
              self_ "a" #= 2
              ]
            ],
          self_ "a" #= env_ "y" #. "x" # [ self_ "a" #= 1env_ "y" #. "a"
          ] #. "a")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
-}
    ]