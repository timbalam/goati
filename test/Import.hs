{-# LANGUAGE OverloadedStrings #-}

module Import
  ( importTests
  )
  where

import My.Eval
import My.Types.Expr
import My.Types.Parser.Short
import qualified My.Types.Parser as P
import My.Parser (ShowMy, showMy)
import qualified My
import Data.List.NonEmpty( NonEmpty )
import Data.Foldable( asum )
import Data.Void
import Data.Maybe( fromMaybe )
import qualified Data.Map as M
import Control.Monad( (<=<) )
import Control.Exception
import Test.HUnit
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","

run :: P.Expr (P.Name Ident Key P.Import) -> IO (Expr K (P.Vis Ident Key))
run r = eval <$> My.loadExpr r ["test/data"]

importTests =
  test
    [ "import resolves to local .my file with same name" ~: let
        r = use_ "import" #. "test"
        e = String "imported"
        in
        run r >>= assertEqual (banner r) e
        
    , "imported file resolves nested imports to directory with same name" ~: let
        r = use_ "chain" #. "test"
        e = String "nested"
        in
        run r >>= assertEqual (banner r) e
    ]
    
    