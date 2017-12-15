{-# LANGUAGE OverloadedStrings #-}
module Test.Eval
  ( tests
  )
  where

import qualified Core
import qualified Eval as Core
import qualified Types.Core as Core
import Types.Classes
import Types.Parser.Short
--import qualified Types.Error as E

import qualified Data.Map as M
import Test.HUnit hiding ( Label )
import Bound( closed )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: Core.Expr a -> IO (Core.Expr a)
run e = do
  e <- maybe 
    (ioError (userError "closed"))
    return
    (closed e)
  maybe
    (ioError (userError "eval"))
    return
    (Core.eval e)


fails :: Show a => (e -> Assertion) -> Core.Expr a -> Assertion
fails _ e =
  maybe
    (return ())
    (ioError . userError . show)
    (Core.eval e)
  
  
parses :: Syntax -> IO (Core.Expr (Vis Core.Id))
parses e = do
  maybe
    (ioError (userError "expr"))
    return
    (Core.getresult (Core.expr e))


tests =
  test
    [ "add" ~: let
        r = (1 #+ 1)
        e = Core.Number 2
        in
        parses r >>= run >>= assertEqual (banner r) e
          
    , "subtract" ~: let
        r = (1 #- 2)
        e = Core.Number (-1)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "public variable" ~: let
        r = (block' [ self' "pub" #= 1 ] #. "pub")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
       
    , "private variable" ~: let
        r = (block' [ env' "priv" #= 1 ] #. "priv")
        in parses r >>= fails (assertEqual "Unbound var: priv" "priv")
    
    , "private variable access backward" ~: let
        r = (block' [
          env' "priv" #= 1,
          self' "pub" #= env' "priv"
          ] #. "pub")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "private variable access forward" ~: let
        r = (block' [
          self' "pub" #= env' "priv",
          env' "priv" #= 1
          ] #. "pub")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access of public variable" ~: let
        r = (block' [
          self' "a" #= 1,
          self' "b" #= env' "a"
          ] #. "b")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access in nested scope of public variable" ~: let
        r = (block' [
          self' "a" #= 1,
          env' "object" #= block' [ self' "b" #= env' "a" ],
          self' "c" #= env' "object" #. "b"
          ] #. "c")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access backward public variable from same scope" ~: let
        r = (block' [
          self' "b" #= 2,
          self' "a" #= self' "b"
          ] #. "a")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access forward public variable from same scope" ~: let
        r = (block' [
          self' "a" #= self' "b",
          self' "b" #= 2
          ] #. "a")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "nested public access" ~: let
        r = (block' [
            self' "return" #= block' [ self' "return" #= "str" ] #. "return"
          ] #. "return")
        e = Core.String "str"
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "unbound variable" ~: let
        r = (block' [
          self' "a" #= 2,
          self' "b" #= env' "c"
          ] #. "b")
        in parses r >>= fails (assertEqual "Unbound var: c" "c")
          
    , "undefined variable" ~: let
        r = block' [
          Declare (self' "a"),
          self' "b" #= 1
          ]
        in do
        let
          r1 = r #. "b"
          e1 = Core.Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "a"
        parses r2 >>= fails (assertEqual "Unbound var : a" "a")
         
    , "unset variable forwards" ~: let
        r = (block' [
          env' "c" #= 1,
          env' "b" #= block' [
            Declare (env' "c"),
            self' "a" #= env' "c"
            ],
          self' "ba" #= env' "b" #. "a"
          ] #. "ba")
        in parses r >>= fails (assertEqual "Unbound var: c" "c")
          
    , "unset variable backwards" ~: let
        r = (block' [
          env' "c" #= 1,
          env' "b" #= block' [
            self' "a" #= env' "c",
            Declare (env' "c")
            ],
          self' "ba" #= env' "b" #. "a"
          ] #. "ba")
        in parses r >>= fails (assertEqual "Unbound var: c" "c")
    
    , "application  overriding public variable" ~: let
        r = (block' [
          self' "a" #= 2,
          self' "b" #= self' "a"
          ] # block' [ self' "a" #= 1 ] #. "b")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "default definition forward" ~: let
        r = (block' [
          self' "a" #= self' "b",
          self' "b" #= self' "a"
          ] # block' [ self' "b" #= 2 ] #. "a")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "default definition backward" ~: let
        r = (block' [
          self' "a" #= self' "b",
          self' "b" #= self' "a"
          ] # block' [ self' "a" #= 1 ] #. "b")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
         
    , "route getter" ~: let
        r = (block' [
          self' "a" #= block' [ self' "aa" #= 2 ]
          ] #. "a" #. "aa")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "route setter" ~: let
        r = (block' [ self' "a" #. "aa" #= 2 ] #. "a" #. "aa")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
    
    , "application overriding nested property" ~: let
        r = (block' [
          self' "a" #= block' [ self' "aa" #= 0 ],
          self' "b" #= self' "a" #. "aa"
          ] # block' [ self' "a" #. "aa" #= 1 ] #. "b")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
     
    {-
    , "shadowing update" ~: let
        r = (block' [
          env' "a" #= block' [ self' "a" #= 1 ],
          self' "ab" #= block' [
            env' "a" #. "b" #= 2,
            self' "return" #= env' "a"
            ] #. "return"
          ] #. "ab")
        in do
        let
          r1 = r `Core.At` Label "a"
          e1 = Core.Number 1
        parses r >>= run1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` Label "b"
          e2 = Core.Number 2
        parses r >>= run2 >>= assertEqual (banner r2) e2
    
    , "original value is not affected by shadowing" ~: let
        r = (block' [
          env' "ab" #= block' [
            self' "a" #= 2,
            self' "b" #= 1
            ],
          self' "ab2" #= block' [
            env' "ab" #. "b" #= 2,
            self' "return" #= env' "ab"
            ] #. "return",
          self' "ab1" #= env' "ab"
          ])
        in do
        let
          r1 = (r `Core.At` Label "ab1") `Core.At` Label "b"
          e1 = Core.Number 1
        parses r >>= run1 >>= assertEqual (banner r1) e1
        let
          r2 = (r `Core.At` Label "ab2") `Core.At` Label "b"
          e2 = Core.Number 2
        parses r >>= run2 >>= assertEqual (banner r2) e2
    -}
          
    , "destructuring" ~: let
        r = (block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock' [
            self' "a" #= self' "da",
            self' "b" #= self' "db"
            ] #= env' "obj"
          ])
        in do
        let
          r1 = r #. "da"
          e1 = Core.Number 2
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let 
          r2 = r #. "db"
          e2 = Core.Number 3
        parses r2 >>= run >>= assertEqual (banner r2) e2
            
    , "destructuring unpack" ~: let
        r = (block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock'' [] (self' "d") #= env' "obj"
          ] #. "d" #. "b")
        e = Core.Number 3
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "nested destructuring" ~: let
        r = (block' [
          env' "y1" #= block' [
            self' "a" #= block' [
              self' "aa" #= 3,
              self' "ab" #= block' [ self' "aba" #= 4 ]
              ]
            ],
          setblock' [
            self' "a" #. "aa" #= self' "da",
            self' "a" #. "ab" #. "aba" #= self' "daba"
            ] #= env' "y1",
          self' "raba" #= env' "y1" #. "a" #. "ab" #. "aba"
          ])
        in do
        let
          r1 = r #. "raba"
          e1 = Core.Number 4
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "daba"
          e2 = Core.Number 4
        parses r2 >>= run >>= assertEqual (banner r2) e2
      
    , "self references valid in extensions to an object" ~: let
        r = block' [
          env' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= self' "a" ]
            (env' "w1"),
          self' "w3" #= self' "w2" #. "a"
          ]
        in do
        let
          r1 = r #. "w2" #. "b"
          e1 = Core.Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "w3"
          e2 = Core.Number 1
        parses r2 >>= run >>= assertEqual (banner r2) e2
        
    , "object fields not in private scope for extensions to an object" ~: let
        r = (block' [
          env' "a" #= 2,
          env' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= env' "a" ]
            (env' "w1")
          ] #. "w2" #. "b")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access extension field of extended object" ~: let
        r = (block' [
          self' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= 2 ]
            (self' "w1")
          ] #. "w2" #. "b")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
            
    , "parent scope binding" ~: let
        r = (block' [
          self' "inner" #= 1,
          env' "parInner" #= self' "inner",
          self' "outer" #= block' [
            self' "inner" #= 2,
            self' "a" #= env' "parInner"
            ]       
          ] #. "outer" #. "a")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "extension scope binding" ~: let
        r = (block' [
          env' "inner" #= block' [
            env' "var" #= 1,
            self' "innerVar" #= env' "var"
            ],
          env' "outer" #= block''
            [ env' "var" #= 2 ]
            (env' "inner"),
          self' "a" #= env' "outer" #. "innerVar"
          ] #. "a")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "self referencing definition" ~: let
        r = (block' [
          env' "y" #= block' [
            self' "a" #= env' "y" #. "b",
            self' "b" #= 1
            ],
          self' "z" #= env' "y" #. "a"
          ] #. "z")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "application to referenced outer scope" ~: let
        r = (block' [
          env' "y" #= block' [
            self' "a" #= 1,
            env' "b" #= 2,
            self' "x" #= block' [ self' "a" #= env' "b" ]
            ],
          self' "a" #= env' "y" # (env' "y" #. "x") #. "a"
          ] #. "a")
        e = Core.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "application to nested object" ~: let
        r = (block' [
          env' "y" #= block' [
            self' "a" #= 1,
            self' "x" #= block' [
              self' "a" #= 2,
              Declare (self' "x")
              ]
            ],
          self' "a" #= env' "y" #. "x" # env' "y" #. "a"
          ] #. "a")
        e = Core.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
        
    ]