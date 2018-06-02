{-# LANGUAGE OverloadedStrings #-}

module Syntax.Type.IO
  ( tests
  )
  where

import My.Expr
import My.Eval (K)
import My.Eval.IO (evalIO)
import My.Base (defaultBase)
import My.Types.Expr
import My.Types.Parser.Short
import qualified My.Types.Parser as P
import My.Parser (ShowMy, showMy)
import qualified My
import My (ScopeError(..))
import Data.List.NonEmpty (NonEmpty)
import Data.Foldable (asum)
import Data.Void
import qualified Data.Map as M
import qualified System.IO.Error as IO
import Control.Exception
import Control.Monad ((<=<))
import Test.HUnit
import qualified System.IO
import System.IO.Silently (hCapture_)
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: Expr K (P.Vis Ident Key) -> IO ()
run = either 
  (ioError . userError . displayException
    . My.MyExceptions :: [ScopeError] -> IO a)
  evalIO
  . My.applybase defaultBase
  
  
fails :: ([ScopeError] -> Assertion) -> Expr K (P.Vis Ident Key) -> Assertion
fails f = either f (ioError . userError . shows "Unexpected" 
  . show :: Expr K Void -> Assertion)
  . My.applybase defaultBase
  
  
parses :: P.Expr (P.Name Ident Key P.Import) -> IO (Expr K (P.Vis Ident Key))
parses e = My.loadExpr e []


tests =
  test
    [ "stdout" ~: let
        r = env_ "stdout" #. "putStr" # tup_ [
          self_ "val" #= "hello stdout!"
          ] #. "then"
        in
        parses r >>= hCapture_ [System.IO.stdout] . run
          >>= assertEqual "" "hello stdout!"
   
    , "openFile" ~: let
        r = env_ "openFile" # block_ [
          self_ "filename" #= "test/data/IO/file.txt",
          self_ "onSuccess" #= self_ "getContents"
          ] #. "then" # block_ [
          self_ "onSuccess" #= env_ "stdout" #. "putStr" # tup_ [
            self_ "val" #= self_ "val"
            ]
          ] #. "then"
        in
        parses r >>= hCapture_ [System.IO.stdout] . run
          >>= assertEqual "" "string\n"
    ]