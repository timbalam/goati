{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Import
  ( tests
  )
  where

import My.Eval (simplify, K)
import My.Types.Repr (Repr(..), Prim(..))
import My.Types.Syntax.Class
import My.Syntax.Parser (Printer, showP)
import Test.HUnit

banner :: Printer -> String
banner r = "For " ++ showP r ","

run :: ([FilePath] -> IO (Repr K b)) -> IO (Repr K b)
run find = simplify <$> find ["test/data/Import"]


tests
  :: (Syntax a, Eq b, Show b)
  => (a -> [FilePath] -> IO (Repr K b))
  -> Test
tests load =
  test
    [ "import resolves to local .my file with same name" ~: let
        r :: Syntax a => a
        r = use_ "import" #. "test"
        e = Prim (Text "imported")
        in
        run (load r) >>= assertEqual (banner r) e
        
    , "imported file resolves nested imports to directory with same name" ~: let
        r :: Syntax a => a
        r = use_ "chain" #. "test"
        e = Prim (Text "nested")
        in
        run (load r) >>= assertEqual (banner r) e
    ]
    
    