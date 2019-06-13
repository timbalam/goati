{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts, ScopedTypeVariables, OverloadedLists #-}

module Lang.Eval.IO (tests) where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( CanonDefinition, showDefinition, toDefinition
  , unself
  )
import Test.HUnit
import System.IO (stdout)
import System.IO.Silently (hCapture_)
  
banner :: CanonDefinition -> String
banner r
  = "For "
 ++ showDefinition (toDefinition (unself r)) ","


run :: IO a -> IO String
run = hCapture_ [stdout]

tests :: Definition_ a => (a -> IO b) -> Test
tests eval =
  TestList
  [ "write to stdout"
     ~: let
        r :: Definition_ a => a
        r = use_ "io" #. "stdout" #. "putText" # [
          "" #. "text" #= quote_ "hello stdout!"
          ] #. "run"
        e = "hello stdout!"
        in do
          a <- run (eval r)
          assertEqual (banner r) e a
        
  , "read matches \"ifRead\" handler"
     ~: let
        r :: Definition_ a => a
        r = use_ "ioMode" #. "read" # [
          "" #. "ifRead" #= 
            use_ "io" #. "stdout" #.
              "putText" # [
              "" #. "text" #=
                quote_ "read mode"
              ] #. "run"
          ] #. "match"
        e = "read mode"
        in do
          a <- run (eval r)
          assertEqual (banner r) e a
      
  , "write matches \"ifWrite\" handler"
     ~: let
        r :: Definition_ a => a
        r = use_ "io" #. "stdout" #. "putText" #  [
          "" #. "text" #=
            use_ "ioMode" #. "write" # [
              "" #. "ifRead" #= "read mode",
              "" #. "ifWrite" #= "write mode"
              ] #. "match"
          ] #. "run"
        e = "write mode"
        in do
          a <- run (eval r)
          assertEqual (banner r) e a
 
  , "openFile" ~: let
      r :: Definition_ a => a
      r = use_ "io" #. "openFile" # [
        "" #. "file" #= "test/data/IO/file.txt",
        "" #. "mode" #= use_ "ioMode" #. "read",
        "" #. "onSuccess" #=
          "" #. "getContents" # [
            "" #. "onSuccess" #= 
              use_ "io" #. "stdout" #. "putText" # [
              "" #. "text" #= "t"
              ] #. "run",
            "t" #= "" #. "text"
            ] #. "run"
        ] #. "run"
      e = "string\n"
      in do
        a <- run (eval r)
        assertEqual (banner r) e a
  
  ]