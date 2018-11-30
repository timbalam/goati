{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts, ScopedTypeVariables #-}

module Syntax.Eval.IO
  ( tests )
  where

import Goat.Syntax.Class
import Goat.Syntax.Parser (Printer, showP)
import qualified Goat.Syntax.Syntax as P
import Test.HUnit
import System.IO (stdout)
import System.IO.Silently (hCapture_)
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


run :: IO a -> IO String
run = hCapture_ [stdout]

tests :: (Expr a, Extern a) => (a -> IO b) -> Test
tests eval =
  test
    [ "stdout" ~: let
        r :: (Expr a, Extern a) => a
        r = use_ "io" #. "stdout" #. "putText" # block_
          [ self_ "text" #= "hello stdout!" ]
          #. "run"
        e = "hello stdout!"
        in run (eval r) >>= assertEqual (banner r) e
        
    , "ioMode" ~:
      [ "read matches \"ifRead\" handler" ~: let
          r :: (Expr a, Extern a) => a
          r = use_ "ioMode" #. "read" # block_
            [ self_ "ifRead" #= 
              use_ "io" #. "stdout" #. "putText" # block_ 
                [ self_ "text" #= "read mode" ]
                #. "run"
            ]
            #. "match"
          e = "read mode"
          in run (eval r) >>= assertEqual (banner r) e
        
      , "write matches \"ifWrite\" handler" ~: let
          r :: (Expr a, Extern a) => a
          r = use_ "io" #. "stdout" #. "putText" # block_
            [ self_ "text" #=
                use_ "ioMode" #. "write" # block_ 
                  [ self_ "ifRead" #= "read mode"
                  , self_ "ifWrite" #= "write mode"
                  ] #. "match"
            ] #. "run"
          e = "write mode"
          in run (eval r) >>= assertEqual (banner r) e
          
      ]
   
    , "openFile" ~: let
        r :: (Expr a, Extern a) => a
        r = use_ "io" #. "openFile" # block_
          [ self_ "file" #= "test/data/IO/file.txt"
          , self_ "mode" #= use_ "ioMode" #. "read"
          , self_ "onSuccess" #=
              self_ "getContents" # block_
                [ self_ "onSuccess" #= 
                    use_ "io" #. "stdout" #. "putText" # block_
                      [ self_ "text" #= esc_ (self_ "text") ] #. "run"
                ] #. "run"
          ] #. "run"
        e = "string\n"
        in run (eval r) >>= assertEqual (banner r) e
    
    ]