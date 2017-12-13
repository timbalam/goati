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
    [ "add" ~: do
        r <- parses (1 #+ 1)
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "subtract" ~: do
        r <- parses (1 #- 2)
        let e = Core.Number (-1)
        run r >>= assertEqual (banner r) e
          
    , "public variable" ~: do
        r <- parses (block' [ self' "pub" #= 1 ] #. "pub")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
       
    , "private variable" ~: do
        r <- parses (block' [ env' "priv" #= 1 ] #. "priv")
        fails (assertEqual "Unbound var: priv" "priv") r
    
    , "private variable access backward" ~: do
        r <- parses (block' [
          env' "priv" #= 1,
          self' "pub" #= env' "priv"
          ] #. "pub")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
        
    , "private variable access forward" ~: do
        r <- parses (block' [
          self' "pub" #= env' "priv",
          env' "priv" #= 1
          ] #. "pub")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "private access of public variable" ~: do
        r <- parses (block' [
          self' "a" #= 1,
          self' "b" #= env' "a"
          ] #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "private access in nested scope of public variable" ~: do
        r <- parses (block' [
          self' "a" #= 1,
          env' "object" #= block' [ self' "b" #= env' "a" ],
          self' "c" #= env' "object" #. "b"
          ] #. "c")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "access backward public variable from same scope" ~: do
        r <- parses (block' [
          self' "b" #= 2,
          self' "a" #= self' "b"
          ] #. "a")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "access forward public variable from same scope" ~: do
        r <- parses (block' [
          self' "a" #= self' "b",
          self' "b" #= 2
          ] #. "a")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
        
    , "nested public access" ~: do
        r <- parses (block' [
            self' "return" #= block' [ self' "return" #= "str" ] #. "return"
          ] #. "return")
        let e = Core.String "str"
        run r >>= assertEqual (banner r) e
          
    , "unbound variable" ~: do
        r <- parses (block' [
          self' "a" #= 2,
          self' "b" #= env' "c"
          ] #. "b")
        fails (assertEqual "Unbound var: c" "c") r
          
    , "undefined variable" ~: do
        r <- (parses . block') [
          Declare (self' "a"),
          self' "b" #= 1
          ]
        let
          r1 = r `Core.At` Label "b"
          e1 = Core.Number 1
          r2 = r `Core.At` Label "a"
        run r1 >>= assertEqual (banner r1) e1
        fails (assertEqual "Unbound var : a" "a") r2
         
    , "unset variable forwards" ~: do
        r <- parses (block' [
          env' "c" #= 1,
          env' "b" #= block' [
            Declare (env' "c"),
            self' "a" #= env' "c"
            ],
          self' "ba" #= env' "b" #. "a"
          ] #. "ba")
        fails (assertEqual "Unbound var: c" "c") r
          
    , "unset variable backwards" ~: do
        r <- parses (block' [
          env' "c" #= 1,
          env' "b" #= block' [
            self' "a" #= env' "c",
            Declare (env' "c")
            ],
          self' "ba" #= env' "b" #. "a"
          ] #. "ba")
        fails (assertEqual "Unbound var: c" "c") r
    
    , "application  overriding public variable" ~: do
        r <- parses (block' [
          self' "a" #= 2,
          self' "b" #= self' "a"
          ] # block' [ self' "a" #= 1 ] #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "default definition forward" ~: do
        r <- parses (block' [
          self' "a" #= self' "b",
          self' "b" #= self' "a"
          ] # block' [ self' "b" #= 2 ] #. "a")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
        
    , "default definition backward" ~: do
        r <- parses (block' [
          self' "a" #= self' "b",
          self' "b" #= self' "a"
          ] # block' [ self' "a" #= 1 ] #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
         
    , "route getter" ~: do
        r <- parses (block' [
          self' "a" #= block' [ self' "aa" #= 2 ]
          ] #. "a" #. "aa")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "route setter" ~: do
        r <- parses (block' [ self' "a" #. "aa" #= 2 ] #. "a" #. "aa")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
    
    , "application overriding nested property" ~: do
        r <- parses (block' [
          self' "a" #= block' [ self' "aa" #= 0 ],
          self' "b" #= self' "a" #. "aa"
          ] # block' [ self' "a" #. "aa" #= 1 ] #. "b")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
     
    {-
    , "shadowing update" ~: do
        r <- parses (block' [
          env' "a" #= block' [ self' "a" #= 1 ],
          self' "ab" #= block' [
            env' "a" #. "b" #= 2,
            self' "return" #= env' "a"
            ] #. "return"
          ] #. "ab")
        let
          r1 = r `Core.At` Label "a"
          e1 = Core.Number 1
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` Label "b"
          e2 = Core.Number 2
        run r2 >>= assertEqual (banner r2) e2
    
    , "original value is not affected by shadowing" ~: do
        r <- parses (block' [
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
        let
          r1 = (r `Core.At` Label "ab1") `Core.At` Label "b"
          e1 = Core.Number 1
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = (r `Core.At` Label "ab2") `Core.At` Label "b"
          e2 = Core.Number 2
        run r2 >>= assertEqual (banner r2) e2
    -}
          
    , "destructuring" ~: do
        r <- parses (block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock' [
            self' "a" #= self' "da",
            self' "b" #= self' "db"
            ] #= env' "obj"
          ])
        let
          r1 = r `Core.At` Label "da"
          e1 = Core.Number 2
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` Label "db"
          e2 = Core.Number 3
        run r2 >>= assertEqual (banner r2) e2
            
    , "destructuring unpack" ~: do
        r <- parses (block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock'' [] (self' "d") #= env' "obj"
          ] #. "d" #. "b")
        let
          e = Core.Number 3
        run r >>= assertEqual (banner r) e
          
    , "nested destructuring" ~: do
        r <- parses (block' [
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
        let
          r1 = r `Core.At` Label "raba"
          e1 = Core.Number 4
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` Label "daba"
          e2 = Core.Number 4
        run r2 >>= assertEqual (banner r2) e2
      
    , "self references valid in extensions to an object" ~: do
        r <- (parses . block') [
          env' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= self' "a" ]
            (env' "w1"),
          self' "w3" #= self' "w2" #. "a"
          ]
        let
          r1 = (r `Core.At` Label "w2") `Core.At` Label "b"
          e1 = Core.Number 1
        run r1 >>= assertEqual (banner r1) e1
        let
          r2 = r `Core.At` Label "w3"
          e2 = Core.Number 1
        run r2 >>= assertEqual (banner r2) e2
        
    , "object fields not in private scope for extensions to an object" ~: do
        r <- parses (block' [
          env' "a" #= 2,
          env' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= env' "a" ]
            (env' "w1")
          ] #. "w2" #. "b")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "access extension field of extended object" ~: do
        r <- parses (block' [
          self' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= 2 ]
            (self' "w1")
          ] #. "w2" #. "b")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
            
    , "parent scope binding" ~: do
        r <- parses (block' [
          self' "inner" #= 1,
          env' "parInner" #= self' "inner",
          self' "outer" #= block' [
            self' "inner" #= 2,
            self' "a" #= env' "parInner"
            ]       
          ] #. "outer" #. "a")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "extension scope binding" ~: do
        r <- parses (block' [
          env' "inner" #= block' [
            env' "var" #= 1,
            self' "innerVar" #= env' "var"
            ],
          env' "outer" #= block''
            [ env' "var" #= 2 ]
            (env' "inner"),
          self' "a" #= env' "outer" #. "innerVar"
          ] #. "a")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "self referencing definition" ~: do
        r <- parses (block' [
          env' "y" #= block' [
            self' "a" #= env' "y" #. "b",
            self' "b" #= 1
            ],
          self' "z" #= env' "y" #. "a"
          ] #. "z")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
          
    , "application to referenced outer scope" ~: do
        r <- parses (block' [
          env' "y" #= block' [
            self' "a" #= 1,
            env' "b" #= 2,
            self' "x" #= block' [ self' "a" #= env' "b" ]
            ],
          self' "a" #= env' "y" # (env' "y" #. "x") #. "a"
          ] #. "a")
        let e = Core.Number 2
        run r >>= assertEqual (banner r) e
          
    , "application to nested object" ~: do
        r <- parses (block' [
          env' "y" #= block' [
            self' "a" #= 1,
            self' "x" #= block' [
              self' "a" #= 2,
              Declare (self' "x")
              ]
            ],
          self' "a" #= env' "y" #. "x" # env' "y" #. "a"
          ] #. "a")
        let e = Core.Number 1
        run r >>= assertEqual (banner r) e
    ]