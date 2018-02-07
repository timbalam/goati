{-# LANGUAGE OverloadedStrings #-}
module Test.Eval
  ( tests
  )
  where

import Expr
import Eval
import Types.Expr
--import Types.Classes
import Types.Parser.Short
import qualified Types.Parser as P
import Lib( Ex )

import Data.List.NonEmpty( NonEmpty )
import Data.Foldable( asum )
import Data.Void
import qualified Data.Map as M
import qualified System.IO.Error as IO
import Control.Exception
import Test.HUnit hiding ( Label )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: Ex a -> Ex a
run = eval
  
  
parses :: P.Syntax -> IO (Ex a)
parses = either (ioError . userError . displayException . MyExceptions) return
  . resolveClosed Nothing


tests =
  test
    [ "add ##todo implement" ~: let
        r = (1 #+ 1)
        e = Number 2
        in
        parses r >>= run >>= assertEqual (banner r) e
          
    , "subtract ##todo implement" ~: let
        r = (1 #- 2)
        e = Number (-1)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "public variable" ~: let
        r = (P.Block [ self_ "pub" #= 1 ] #. "pub")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
       
    , "private variable ##todo type error" ~: let
        r = (P.Block [ env_ "priv" #= 1 ] #. "priv")
        in
        parses r >>= run >>= assertFailure . show
    
    , "private variable access backward" ~: let
        r = (P.Block [
          env_ "priv" #= 1,
          self_ "pub" #= env_ "priv"
          ] #. "pub")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "private variable access forward" ~: let
        r = (P.Block [
          self_ "pub" #= env_ "priv",
          env_ "priv" #= 1
          ] #. "pub")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access of public variable" ~: let
        r = (P.Block [
          self_ "a" #= 1,
          self_ "b" #= env_ "a"
          ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access in nested scope of public variable" ~: let
        r = (P.Block [
          self_ "a" #= 1,
          env_ "object" #= P.Block [ self_ "b" #= env_ "a" ],
          self_ "c" #= env_ "object" #. "b"
          ] #. "c")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access backward public variable from same scope" ~: let
        r = (P.Block [
          self_ "b" #= 2,
          self_ "a" #= self_ "b"
          ] #. "a")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access forward public variable from same scope" ~: let
        r = (P.Block [
          self_ "a" #= self_ "b",
          self_ "b" #= 2
          ] #. "a")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "nested public access" ~: let
        r = (P.Block [
          self_ "return" #=
            P.Block [ self_ "return" #= "str" ] #. "return"
          ] #. "return")
        e = String "str"
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "unbound variable" ~: let
        r = (P.Block [
          self_ "a" #= 2,
          self_ "b" #= env_ "c"
          ] #. "b")
        in
        parses r >>= (unclosed . assertEqual "Unbound var: c" . pure . ParamFree) (P.Priv "c")
          
    , "undefined variable ##todo type error" ~: let
        r = P.Block [
          self_ "b" #= self_ "a"
          ] #. "b"
        in
        parses r >>= run >>= assertFailure . show
    
    , "application  overriding public variable" ~: let
        r = (P.Block [
          self_ "a" #= 2,
          self_ "b" #= self_ "a"
          ] # [ self_ "a" #= 1 ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "default definition forward" ~: let
        r = (P.Block [
          self_ "a" #= self_ "b",
          self_ "b" #= self_ "a"
          ] # [ self_ "b" #= 2 ] #. "a")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "default definition backward" ~: let
        r = (P.Block [
          self_ "a" #= self_ "b",
          self_ "b" #= self_ "a"
          ] # [ self_ "a" #= 1 ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
         
    , "route getter" ~: let
        r = (P.Block [
          self_ "a" #= P.Block [ self_ "aa" #= 2 ]
          ] #. "a" #. "aa")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "route setter" ~: let
        r = (P.Block [ self_ "a" #. "aa" #= 2 ] #. "a" #. "aa")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
    
    , "application overriding nested property" ~: let
        r = (P.Block [
          self_ "a" #= P.Block [ self_ "aa" #= 0 ],
          self_ "b" #= self_ "a" #. "aa"
          ] # [ self_ "a" #. "aa" #= 1 ] #. "b")
        e = Number 1
        in parses r >>= run >>= assertEqual (banner r) e
     
    , "shadowing update ##todo implement" ~: let
        r = P.Block [
          env_ "x" #= P.Block [
            self_ "a" #= 1
            ],
          self_ "y" #= P.Block [
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
        r = (P.Block [
          env_ "x" #= P.Block [
            self_ "a" #= 2,
            self_ "b" #= 1
            ],
          self_ "x2" #= P.Block [
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
        r = (P.Block [
          env_ "obj" #= P.Block [
            self_ "a" #= 2,
            self_ "b" #= 3
            ],
          P.SetBlock [
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
        r = (P.Block [
          env_ "obj" #= P.Block [
            self_ "a" #= 2,
            self_ "b" #= 3
            ],
          [] #... self_ "d" #= env_ "obj"
          ] #. "d" #. "b")
        e = Number 3
        in parses r >>= run >>= assertEqual (banner r) e
       
    , "nested destructuring" ~: let
        r = (P.Block [
          env_ "y1" #= P.Block [
            self_ "a" #= P.Block [
              self_ "aa" #= 3,
              self_ "ab" #= P.Block [ self_ "aba" #= 4 ]
              ]
            ],
          P.SetBlock [
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
        r = P.Block [
          env_ "w1" #= P.Block [ self_ "a" #= 1 ],
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
        r = (P.Block [
          env_ "a" #= 2,
          env_ "w1" #= P.Block [ self_ "a" #= 1 ],
          self_ "w2" #= env_ "w1" # [ self_ "b" #= env_ "a" ]
          ] #. "w2" #. "b")
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access extension field of extended object" ~: let
        r = P.Block [
          self_ "w1" #= P.Block [ self_ "a" #= 1 ],
          self_ "w2" #= self_ "w1" # [ self_ "b" #= 2 ]
          ] #. "w2" #. "b"
        e = Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "extension private field scope do not shadow fields of original" ~: let
        r = P.Block [
          env_ "original" #= P.Block [
            env_ "priv" #= 1,
            self_ "privVal" #= env_ "priv"
            ],
          env_ "new" #= env_ "original" #
            [ env_ "priv" #= 2 ],
          self_ "call" #= env_ "new" #. "privVal"
          ] #. "call"
        v = Number 1
        in parses r >>= run >>= assertEqual (banner r) v
          
    , "self referencing definition" ~: let
        r = P.Block [
          env_ "y" #= P.Block [
            self_ "a" #= env_ "y" #. "b",
            self_ "b" #= 1
            ],
          self_ "call" #= env_ "y" #. "a"
          ] #. "call"
        v = Number 1
        in parses r >>= run >>= assertEqual (banner r) v
   
    , "extension referencing original version" ~: let
        r = P.Block [
          env_ "y" #= P.Block [ self_ "a" #= 1 ],
          self_ "call" #= env_ "y" # [
            self_ "a" #= env_ "y" #. "a"
            ] #. "a"
          ] #. "call"
        v = Number 1
        in parses r >>= run >>= assertEqual (banner r) v
        
    ]