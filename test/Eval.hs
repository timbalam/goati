{-# LANGUAGE OverloadedStrings #-}

module Eval
  ( tests
  )
  where

import My.Eval (simplify, K)
import My.Types.Expr (Expr(..), Prim(..))
import My.Types.Syntax.Class hiding (Expr)
import qualified My.Types.Syntax.Class as S (Expr)
import My.Syntax.Parser (Printer, showP)
import qualified My.Types.Parser as P
import My (ScopeError(..), MyException(..))
import Data.Void (Void)
import Control.Exception (ioError, displayException)
import Test.HUnit
  
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


run :: Either [ScopeError] (Expr K Void) -> IO (Expr K Void)
run = either 
  (ioError . userError . displayException
    . MyExceptions :: [ScopeError] -> IO a)
  (return . simplify)
  
  
fails :: ([ScopeError] -> Assertion) -> Either [ScopeError] (Expr K Void) -> Assertion
fails f = either f (ioError . userError . shows "Unexpected: " . show)


tests
  :: S.Expr a
  => (a -> IO (Either [ScopeError] (Expr K Void)))
  -> Test
tests parses =
  test
    [ "add" ~: let
        r :: (Num a, Lit a) => a
        r = (1 #+ 1)
        e = Prim (Number 2)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "subtract" ~: let
        r :: (Num a, Lit a) => a
        r = (1 #- 2)
        e = (Prim . Number) (-1)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "public variable" ~: let
        r :: S.Expr a => a
        r = block_ ( self_ "pub" #= 1 ) #. "pub"
        e = Prim (Number 1)
        in parses r >>= run >>= assertEqual (banner r) e
       
    , "private variable ##todo type error" ~: let
        r :: S.Expr a => a
        r = block_ ( local_ "priv" #= 1 ) #. "priv"
        in parses r >>= run >>= assertFailure . show
    
    , "private variable access backward" ~: let
        r :: S.Expr a => a
        r = block_ (
          local_ "priv" #= 1 #:
          self_ "pub" #= local_ "priv"
          ) #. "pub"
        e = Prim (Number 1)
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "private variable access forward" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "pub" #= local_ "priv" #:
          local_ "priv" #= 1
          ) #. "pub"
        e = Prim (Number 1)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access of public variable" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= 1 #:
          self_ "b" #= local_ "a"
          ) #. "b"
        e = Prim (Number 1)
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "private access in nested scope of public variable" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= 1 #:
          local_ "object" #= block_ ( self_ "b" #= local_ "a" ) #:
          self_ "c" #= local_ "object" #. "b"
          ) #. "c"
        e = (Prim . Number) 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access backward public variable from same scope" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "b" #= 2 #:
          self_ "a" #= self_ "b"
          ) #. "a"
        e = (Prim . Number) 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access forward public variable from same scope" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= self_ "b" #:
          self_ "b" #= 2
          ) #. "a"
        e = (Prim . Number) 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "nested public access" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "return" #=
            block_ ( self_ "return" #= "str" ) #. "return"
          ) #. "return"
        e = Prim (String "str")
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "unbound variable" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= 2 #:
          self_ "b" #= local_ "c"
          ) #. "b"
        e = [FreeParam (P.Priv "c")]
        in parses r >>= fails (assertEqual (banner r) e)
          
    , "undefined variable ##todo type error" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "b" #= self_ "a"
          ) #. "b"
        in parses r >>= run >>= assertFailure . show
    
    , "application  overriding public variable" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= 2 #:
          self_ "b" #= self_ "a"
          ) # block_ ( self_ "a" #= 1 ) #. "b"
        e = (Prim . Number) 1
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "default definition forward" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= self_ "b" #:
          self_ "b" #= self_ "a"
          ) # block_ ( self_ "b" #= 2 ) #. "a"
        e = (Prim . Number) 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "default definition backward" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= self_ "b" #:
          self_ "b" #= self_ "a"
          ) # block_ ( self_ "a" #= 1 ) #. "b"
        e = (Prim . Number) 1
        in parses r >>= run >>= assertEqual (banner r) e
         
    , "route getter" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= block_ ( self_ "aa" #= 2 )
          ) #. "a" #. "aa"
        e = (Prim . Number) 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "route setter" ~: let
        r :: S.Expr a => a
        r = block_ ( self_ "a" #. "aa" #= 2 ) #. "a" #. "aa"
        e = (Prim . Number) 2
        in parses r >>= run >>= assertEqual (banner r) e
    
    , "application overriding nested property" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "a" #= block_ ( self_ "aa" #= 0 ) #:
          self_ "b" #= self_ "a" #. "aa"
          ) # block_ ( self_ "a" #. "aa" #= 1 ) #. "b"
        e = (Prim . Number) 1
        in parses r >>= run >>= assertEqual (banner r) e
     
    , "shadowing update" ~: let
        r, r1, r2 :: S.Expr a => a
        r = block_ (
          local_ "x" #= block_ (
            self_ "a" #= 1
            ) #:
          self_ "y" #= block_ (
            local_ "x" #. "b" #= 2 #:
            self_ "return" #= local_ "x"
            ) #. "return"
          ) #. "y"
        r1 = r #."a"
        r2 = r #. "b"
        e1 = (Prim . Number) 1
        e2 = (Prim . Number) 2
        in do
          parses r1 >>= run >>= assertEqual (banner r1) e1
          parses r2 >>= run >>= assertEqual (banner r2) e2
    
    , "original value is not affected by shadowing" ~: let
        r, r1, r2 :: S.Expr a => a
        r = block_ (
          local_ "x" #= block_ (
            self_ "a" #= 2 #:
            self_ "b" #= 1
            ) #:
          self_ "x2" #= block_ (
            local_ "x" #. "b" #= 2 #:
            self_ "return" #= local_ "x"
            ) #. "return" #:
          self_ "x1" #= local_ "x"
          )
        r1 = r #. "x1" #. "b"
        r2 = r #. "x2" #. "b"
        e1 = (Prim . Number) 1
        e2 = (Prim . Number) 2
        in do 
          parses r1 >>= run >>= assertEqual (banner r1) e1
          parses r2 >>= run >>= assertEqual (banner r2) e2
          
    , "destructuring" ~: let
        r, r1, r2 :: S.Expr a => a
        r = block_ (
          local_ "obj" #= block_ (
            self_ "a" #= 2 #:
            self_ "b" #= 3
            ) #:
          tup_ (
            self_ "a" #= self_ "da" #:
            self_ "b" #= self_ "db"
            ) #= local_ "obj"
          )
        r1 = r #. "da"
        r2 = r #. "db"
        e1 = (Prim . Number) 2
        e2 = (Prim . Number) 3
        in do
          parses r1 >>= run >>= assertEqual (banner r1) e1
          parses r2 >>= run >>= assertEqual (banner r2) e2
    
    , "destructuring unpack" ~: let
        r :: S.Expr a => a
        r = block_ (
          local_ "obj" #= block_ (
            self_ "a" #= 2 #:
            self_ "b" #= 3
            ) #:
          self_ "d" # tup_ empty_ #= local_ "obj"
          ) #. "d" #. "b"
        e = (Prim . Number) 3
        in parses r >>= run >>= assertEqual (banner r) e
       
    , "nested destructuring" ~: let
        r, r1, r2 :: S.Expr a => a
        r = block_ (
          local_ "y1" #= block_ (
            self_ "a" #= block_ (
              self_ "aa" #= 3 #:
              self_ "ab" #= block_ ( self_ "aba" #= 4 )
              )
            ) #:
          tup_ (
            self_ "a" #. "aa" #= self_ "da" #:
            self_ "a" #. "ab" #. "aba" #= self_ "daba"
            ) #= local_ "y1" #:
          self_ "raba" #= local_ "y1" #. "a" #. "ab" #. "aba"
          )
        r1 = r #. "raba"
        r2 = r #. "daba"
        e1 = (Prim . Number) 4
        e2 = (Prim . Number) 4
        in do
          parses r1 >>= run >>= assertEqual (banner r1) e1
          parses r2 >>= run >>= assertEqual (banner r2) e2
      
    , "self references valid in extensions to an object" ~: let
        r, r1, r2 :: S.Expr a => a
        r = block_ (
          local_ "w1" #= block_ ( self_ "a" #= 1 ) #:
          self_ "w2" #= local_ "w1" # block_ ( self_ "b" #= self_ "a" ) #:
          self_ "w3" #= self_ "w2" #. "a"
          )
        r1 = r #. "w2" #. "b"
        r2 = r #. "w3"
        e1 = (Prim . Number) 1
        e2 = (Prim . Number) 1
        in do
          parses r1 >>= run >>= assertEqual (banner r1) e1
          parses r2 >>= run >>= assertEqual (banner r2) e2
    
    , "object fields not in private scope for extensions to an object" ~: let
        r :: S.Expr a => a
        r = block_ (
          local_ "a" #= 2 #:
          local_ "w1" #= block_ ( self_ "a" #= 1 ) #:
          self_ "w2" #= local_ "w1" # block_ ( self_ "b" #= local_ "a" )
          ) #. "w2" #. "b"
        e = (Prim . Number) 2
        in parses r >>= run >>= assertEqual (banner r) e
          
    , "access extension field of extended object" ~: let
        r :: S.Expr a => a
        r = block_ (
          self_ "w1" #= block_ ( self_ "a" #= 1 ) #:
          self_ "w2" #= self_ "w1" # block_ ( self_ "b" #= 2 )
          ) #. "w2" #. "b"
        e = (Prim . Number) 2
        in parses r >>= run >>= assertEqual (banner r) e
        
    , "extension private field scope do not shadow fields of original" ~: let
        r :: S.Expr a => a
        r = block_ (
          local_ "original" #= block_ (
            local_ "priv" #= 1 #:
            self_ "privVal" #= local_ "priv"
            ) #:
          local_ "new" #= local_ "original" #
            block_ ( local_ "priv" #= 2 ) #:
          self_ "call" #= local_ "new" #. "privVal"
          ) #. "call"
        v = (Prim . Number) 1
        in parses r >>= run >>= assertEqual (banner r) v
          
    , "self referencing definition" ~: let
        r :: S.Expr a => a
        r = block_ (
          local_ "y" #= block_ (
            self_ "a" #= local_ "y" #. "b" #:
            self_ "b" #= 1
            ) #:
          self_ "call" #= local_ "y" #. "a"
          ) #. "call"
        v = (Prim . Number) 1
        in parses r >>= run >>= assertEqual (banner r) v
   
    , "extension referencing original version" ~: let
        r :: S.Expr a => a
        r = block_ (
          local_ "y" #= block_ ( self_ "a" #= 1 ) #:
          self_ "call" #= local_ "y" # block_ (
            self_ "a" #= local_ "y" #. "a"
            ) #. "a"
          ) #. "call"
        v = (Prim . Number) 1
        in parses r >>= run >>= assertEqual (banner r) v
        
    ]