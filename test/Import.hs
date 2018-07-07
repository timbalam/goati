{-# LANGUAGE OverloadedStrings, TypeFamilies, FlexibleContexts #-}

module Import
  ( tests
  )
  where

import My.Eval (simplify, K)
import My.Types.Expr (Expr(..), ExprT(..), Prim(..))
import My.Types.Syntax.Class hiding (Expr)
import My.Syntax.Parser (Printer, showP)
import Test.HUnit
import Data.Functor.Identity (Identity)

type Expr' k = Expr k Identity

banner :: Printer -> String
banner r = "For " ++ showP r ","

run :: ([FilePath] -> IO (Expr' K b)) -> IO (Expr' K b)
run find = simplify <$> find ["test/data/Import"]


tests
  :: (Syntax a, Eq b, Show b)
  => (a -> [FilePath] -> IO (Expr' K b))
  -> Test
tests load =
  test
    [ "import resolves to local .my file with same name" ~: let
        r :: Syntax a => a
        r = use_ "import" #. "test"
        e = (Expr . return . Prim) (Text "imported")
        in
        run (load r) >>= assertEqual (banner r) e
        
    , "imported file resolves nested imports to directory with same name" ~: let
        r :: Syntax a => a
        r = use_ "chain" #. "test"
        e = (Expr . return . Prim) (Text "nested")
        in
        run (load r) >>= assertEqual (banner r) e
    ]
    
    