{-# LANGUAGE OverloadedStrings #-}
module Test.Import
  ( tests
  )
  where

--import Expr
import Eval
import Types.Expr
--import Types.Classes
import Types.Parser.Short
import qualified Types.Parser as P
import Parser( ShowMy, showMy )
import qualified Lib

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
run r = eval <$> Lib.loadExpr r ["test/data"]

tests =
  test
    [ "import" ~: let
        r = use_ "import" #. "test"
        e = String "imported"
        in
        run r >>= assertEqual (banner r) e
        
    , "chained import" ~: let
        r = use_ "chain" #. "test"
        e = String "nested"
        in
        run r >>= assertEqual (banner r) e
    ]
    
    