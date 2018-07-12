{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module IO
  ( tests
  )
  where

import My.Eval (K)
import My.Eval.IO (evalIO)
import My.Types.Repr (Repr)
import My.Types.Syntax.Class
import My.Syntax.Parser (Printer, showP)
import qualified My.Types.Parser as P
import My.Syntax (ScopeError(..), MyException(..))
import Data.Void (Void)
import Control.Exception (ioError, displayException)
import Test.HUnit
import System.IO (stdout)
import System.IO.Silently (hCapture_)
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


run :: Either [ScopeError] (Repr K Void) -> IO String
run = hCapture_ [stdout]
 . either 
    (ioError . userError . displayException . MyExceptions)
    evalIO
  
  
fails :: ([ScopeError] -> Assertion) -> Either [ScopeError] (Repr K Void) -> Assertion
fails f = either f (ioError . userError . shows "Unexpected: " . show)


tests
  :: Expr a
  => (a -> IO (Either [ScopeError] (Repr K Void)))
  -> Test
tests parses =
  test
    [ "stdout" ~: let
        r :: Expr a => a
        r = local_ "stdout" #. "putStr" # tup_ (
          self_ "val" #= "hello stdout!"
          ) #. "then"
        e = "hello stdout!"
        in parses r >>= run >>= assertEqual (banner r) e
   
    , "openFile" ~: let
        r :: Expr a => a
        r = local_ "openFile" # block_ (
          self_ "filename" #= "test/data/IO/file.txt" #:
          self_ "onSuccess" #= self_ "getContents"
          ) #. "then" # block_ (
          self_ "onSuccess" #= local_ "stdout" #. "putStr" # tup_ (
            self_ "val" #= self_ "val"
            )
          ) #. "then"
        e = "string\n"
        in parses r >>= run >>= assertEqual (banner r) e
    ]