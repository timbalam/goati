{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Import
  ( tests
  )
  where

import Goat.Syntax.Class
import Goat.Syntax.Parser (Printer, showP)
import Test.HUnit

banner :: Printer -> String
banner r = "For " ++ showP r ","

run :: ([FilePath] -> IO b) -> IO b
run find = find ["test/data/Import"]


tests
  :: (Syntax a, Lit b, Eq b, Show b)
  => (a -> [FilePath] -> IO b)
  -> Test
tests load =
  test
    [ "import resolves to local .my file with same name" ~: let
        r :: Syntax a => a
        r = use_ "import" #. "test"
        e = "imported"
        in run (load r) >>= assertEqual (banner r) e
        
    , "imported file resolves nested imports to directory with same name" ~: let
        r :: Syntax a => a
        r = use_ "chain" #. "test"
        e = "nested"
        in run (load r) >>= assertEqual (banner r) e
    ]
    
    