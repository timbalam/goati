{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts, ScopedTypeVariables #-}

module IO
  ( tests
  )
  where

import Goat.Types.Syntax.Class
import Goat.Syntax.Parser (Printer, showP)
import qualified Goat.Types.Syntax as P
--import Goat.Syntax.Old (ScopeError(..), MyException(..))
--import Data.Void (Void)
--import Control.Exception (ioError, displayException)
import Test.HUnit
import System.IO (stdout)
import System.IO.Silently (hCapture_)
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


run :: IO a -> IO String
run = hCapture_ [stdout]

tests :: Expr a => (a -> IO b) -> Test
tests eval =
  test
    [ "stdout" ~: let
        r :: Expr a => a
        r = local_ "io" #. "stdout" #. "putText" # tup_
          [ self_ "text" #: "hello stdout!" ]
          #. "run"
        e = "hello stdout!"
        in run (eval r) >>= assertEqual (banner r) e
        
    , "ioMode" ~:
      [ "read matches \"ifRead\" handler" ~: let
          r :: Expr a => a
          r = local_ "ioMode" #. "read" # tup_
            [ self_ "ifRead" #: 
              local_ "io" #. "stdout" #. "putText" # tup_ 
                [ self_ "text" #: "read mode" ]
                #. "run"
            ]
            #. "match"
          e = "read mode"
          in run (eval r) >>= assertEqual (banner r) e
        
      , "write matches \"ifWrite\" handler" ~: let
          r :: Expr a => a
          r = local_ "io" #. "stdout" #. "putText" # tup_
            [ self_ "text" #:
                local_ "ioMode" #. "write" # tup_ 
                  [ self_ "ifRead" #: "read mode"
                  , self_ "ifWrite" #: "write mode"
                  ] #. "match"
            ] #. "run"
          e = "write mode"
          in run (eval r) >>= assertEqual (banner r) e
          
      ]
   
    , "openFile" ~: let
        r :: Expr a => a
        r = local_ "io" #. "openFile" # block_
          [ self_ "file" #= "test/data/IO/file.txt"
          , self_ "mode" #= local_ "ioMode" #. "read"
          , self_ "onSuccess" #=
              self_ "getContents" # block_
                [ self_ "onSuccess" #= 
                    local_ "io" #. "stdout" #. "putText" # tup_
                      [ self_ "text" #: self_ "text" ] #. "run"
                ] #. "run"
          ] #. "run"
        e = "string\n"
        in run (eval r) >>= assertEqual (banner r) e
    
    ]