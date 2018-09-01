{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module IO
  ( tests
  )
  where

import My.Types.Syntax.Class
import My.Syntax.Parser (Printer, showP)
import qualified My.Types.Parser as P
--import My.Syntax.Old (ScopeError(..), MyException(..))
--import Data.Void (Void)
--import Control.Exception (ioError, displayException)
import Test.HUnit
import System.IO (stdout)
import System.IO.Silently (hCapture_)
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


run :: IO a -> IO String
run = hCapture_ [stdout]

tests
  :: Expr a
  => (a -> IO b)
  -> Test
tests parses =
  test
    [ "stdout" ~: let
        r :: Expr a => a
        r = local_ "stdout" #. "putStr" # tup_ (
          self_ "val" #= "hello stdout!"
          ) #. "then"
        e = "hello stdout!"
        in run (parses r) >>= assertEqual (banner r) e
   
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
        in run (parses r) >>= assertEqual (banner r) e
    ]