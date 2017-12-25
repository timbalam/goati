{-# LANGUAGE OverloadedStrings #-}
module Test.Eval
  ( tests
  )
  where

import qualified Expr
import qualified Eval as Expr
import qualified Types.Expr as Expr
import Types.Classes
import Types.Parser.Short
import Types.Error

import Data.List.NonEmpty( NonEmpty )
import qualified Data.Map as M
import Test.HUnit hiding ( Label )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: Show a => Expr.Expr a -> IO (Expr.Expr a)
run e = do
  e <- either
    (ioError . userError . shows "expr: " . show)
    return
    (Expr.closed e)
  either
    (ioError . userError . shows "eval: " . show)
    return
    (Expr.eval e)
    
    
unclosed :: (NonEmpty (ScopeError Expr.Vid) -> Assertion) -> Expr.Expr Expr.Vid -> Assertion
unclosed f =
  either f (ioError . userError . show :: Expr.Expr Expr.Vid -> IO ())
  . Expr.closed


fails :: Show a => (EvalError Expr.Id -> Assertion) -> Expr.Expr a -> Assertion
fails f =
  either f (ioError . userError . show)
  . Expr.eval
  
  
parses :: Syntax -> IO (Expr.Expr (Vis Expr.Id))
parses =
  either (ioError . userError . shows "expr: " . show)
    return
    . Expr.expr


tests =
  test
    [ "add" ~: let
        r = (1 #+ 1)
        e = Expr.Number 2
        in
        parses r >>= run >>= assertEqual (banner r) e
          
    , "subtract" ~: let
        r = (1 #- 2)
        e = Expr.Number (-1)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "public variable" ~: let
        r = (block' [ self' "pub" #= 1 ] #. "pub")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
       
    , "private variable" ~: let
        r = (block' [ env' "priv" #= 1 ] #. "priv")
        in
        parses r >>= (fails . assertEqual "No field: priv" . LookupFailed) (Label "priv")
    
    , "private variable access backward" ~: let
        r = (block' [
          env' "priv" #= 1,
          self' "pub" #= env' "priv"
          ] #. "pub")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "private variable access forward" ~: let
        r = (block' [
          self' "pub" #= env' "priv",
          env' "priv" #= 1
          ] #. "pub")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access of public variable" ~: let
        r = (block' [
          self' "a" #= 1,
          self' "b" #= env' "a"
          ] #. "b")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access in nested scope of public variable" ~: let
        r = (block' [
          self' "a" #= 1,
          env' "object" #= block' [ self' "b" #= env' "a" ],
          self' "c" #= env' "object" #. "b"
          ] #. "c")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access backward public variable from same scope" ~: let
        r = (block' [
          self' "b" #= 2,
          self' "a" #= self' "b"
          ] #. "a")
        e = Expr.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access forward public variable from same scope" ~: let
        r = (block' [
          self' "a" #= self' "b",
          self' "b" #= 2
          ] #. "a")
        e = Expr.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "nested public access" ~: let
        r = (block' [
            self' "return" #= block' [ self' "return" #= "str" ] #. "return"
          ] #. "return")
        e = Expr.String "str"
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "unbound variable" ~: let
        r = (block' [
          self' "a" #= 2,
          self' "b" #= env' "c"
          ] #. "b")
        in
        parses r >>= (unclosed . assertEqual "Unbound var: c" . pure . ParamFree) (Priv "c")
          
    , "undefined variable" ~: let
        r = block' [
          Declare (self' "a"),
          self' "b" #= 1
          ]
        in do
        let
          r1 = r #. "b"
          e1 = Expr.Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "a"
          e2 = (ParamUndefined . Pub) (Label "a")
        parses r2 >>= fails (assertEqual ""  e2)
         
    , "unset variable forwards" ~: let
        r = (block' [
          env' "c" #= 1,
          env' "b" #= block' [
            Declare (env' "c"),
            self' "a" #= env' "c"
            ],
          self' "ba" #= env' "b" #. "a"
          ] #. "ba")
        e = ParamUndefined (Priv "c")
        in parses r >>= fails (assertEqual "" e)
          
    , "unset variable backwards" ~: let
        r = (block' [
          env' "c" #= 1,
          env' "b" #= block' [
            self' "a" #= env' "c",
            Declare (env' "c")
            ],
          self' "ba" #= env' "b" #. "a"
          ] #. "ba")
        e = ParamUndefined (Priv "c")
        in parses r >>= fails (assertEqual "" e)
    
    , "application  overriding public variable" ~: let
        r = (block' [
          self' "a" #= 2,
          self' "b" #= self' "a"
          ] # block' [ self' "a" #= 1 ] #. "b")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "default definition forward" ~: let
        r = (block' [
          self' "a" #= self' "b",
          self' "b" #= self' "a"
          ] # block' [ self' "b" #= 2 ] #. "a")
        e = Expr.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "default definition backward" ~: let
        r = (block' [
          self' "a" #= self' "b",
          self' "b" #= self' "a"
          ] # block' [ self' "a" #= 1 ] #. "b")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
         
    , "route getter" ~: let
        r = (block' [
          self' "a" #= block' [ self' "aa" #= 2 ]
          ] #. "a" #. "aa")
        e = Expr.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "route setter" ~: let
        r = (block' [ self' "a" #. "aa" #= 2 ] #. "a" #. "aa")
        e = Expr.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
    
    , "application overriding nested property" ~: let
        r = (block' [
          self' "a" #= block' [ self' "aa" #= 0 ],
          self' "b" #= self' "a" #. "aa"
          ] # block' [ self' "a" #. "aa" #= 1 ] #. "b")
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
     
    , "shadowing update" ~: let
        r = block' [
          env' "x" #= block' [
            self' "a" #= 1,
            Declare (self' "b")
            ],
          self' "y" #= block' [
            env' "x" #. "b" #= 2,
            self' "return" #= env' "x"
            ] #. "return"
          ] #. "y"
        in do
        let
          r1 = r #."a"
          e1 = Expr.Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "b"
          e2 = Expr.Number 2
        parses r2 >>= run >>= assertEqual (banner r2) e2
    
    , "original value is not affected by shadowing" ~: let
        r = (block' [
          env' "x" #= block' [
            self' "a" #= 2,
            self' "b" #= 1
            ],
          self' "x2" #= block' [
            env' "x" #. "b" #= 2,
            self' "return" #= env' "x"
            ] #. "return",
          self' "x1" #= env' "x"
          ])
        in do
        let
          r1 = r #. "x1" #. "b"
          e1 = Expr.Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "x2" #. "b"
          e2 = Expr.Number 2
        parses r2 >>= run >>= assertEqual (banner r2) e2
          
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
          e1 = Expr.Number 2
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let 
          r2 = r #. "db"
          e2 = Expr.Number 3
        parses r2 >>= run >>= assertEqual (banner r2) e2
            
    , "destructuring unpack" ~: let
        r = (block' [
          env' "obj" #= block' [
            self' "a" #= 2,
            self' "b" #= 3
            ],
          setblock'' [] (self' "d") #= env' "obj"
          ] #. "d" #. "b")
        e = Expr.Number 3
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
          e1 = Expr.Number 4
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "daba"
          e2 = Expr.Number 4
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
          e1 = Expr.Number 1
        parses r1 >>= run >>= assertEqual (banner r1) e1
        let
          r2 = r #. "w3"
          e2 = Expr.Number 1
        parses r2 >>= run >>= assertEqual (banner r2) e2
        
    , "object fields not in private scope for extensions to an object" ~: let
        r = (block' [
          env' "a" #= 2,
          env' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= env' "a" ]
            (env' "w1")
          ] #. "w2" #. "b")
        e = Expr.Number 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access extension field of extended object" ~: let
        r = (block' [
          self' "w1" #= block' [ self' "a" #= 1 ],
          self' "w2" #= block''
            [ self' "b" #= 2 ]
            (self' "w1")
          ] #. "w2" #. "b")
        e = Expr.Number 2
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
        e = Expr.Number 1
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
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "self referencing definition" ~: let
        r = (block' [
          env' "y" #= block' [
            self' "a" #= env' "y" #. "b",
            self' "b" #= 1
            ],
          self' "z" #= env' "y" #. "a"
          ] #. "z")
        e = Expr.Number 1
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
        e = Expr.Number 2
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
        e = Expr.Number 1
        in parses r >>= run >>= assertEqual (banner r) e
        
    ]