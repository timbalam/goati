{-# LANGUAGE OverloadedStrings #-}

module IO
  ( ioTests
  )
  where

import My.Expr
import My.Eval (evalIO, K, openFile)
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
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: Expr K (P.Vis Ident Key) -> IO (Expr K Void)
run = either 
  (ioError . userError . displayException
    . My.MyExceptions :: [ScopeError] -> IO a)
  (evalIO . (`At` RunIO))
  . My.checkparams
  
  
fails :: ([ScopeError] -> Assertion) -> Expr K (P.Vis Ident Key) -> Assertion
fails f = either f (ioError . userError . shows "Unexpected" 
  . show :: Expr K Void -> Assertion)
  . My.checkparams
  
  
parses :: P.Expr (P.Name Ident Key P.Import) -> IO (Expr K (P.Vis Ident Key))
parses e = My.loadExpr e []


ioTests =
  test
    [ "stdout" ~: let
        r = stdout #. "putStr" # block_ [
          "val" #= "###test#stdout#message"
          ]
        parses r >>= run >> return ()
    
    
    , "openFile" ~: let
        r = (openFile # block_ [
          "filename" #= "file.txt",
          "onSuccess" #= self_ "getContents"
          ] #. "then" # block_ [
          "onSuccess" #= stdout #. "putStr" # tup_ [
            "val" #= self_ "val"
            ]
          ]
        in
        parses r >>= run >>= return ()
   
    ]