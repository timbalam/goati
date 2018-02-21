{-# LANGUAGE OverloadedStrings #-}
module Test.Import
  ( tests
  )
  where

import Expr
import Eval
import Types.Expr
--import Types.Classes
import Types.Parser.Short
import qualified Types.Parser
import Parser( ShowMy, showMy )
--import Types.Error
import Lib
--import Util

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


tests =
  test
    [ "import" ~: let
        r = use_ "import" #. "test"
        e = String "imported"  :: Expr K Void
        in
        loadExpr r ["test/data"] >>= assertEqual (banner r) e . eval
        
    , "chained import" ~: let
        r = use_ "chain" #. "test"
        e = String "nested" :: Expr K Void
        in
        loadExpr r ["test/data"] >>= assertEqual (banner r) e . eval
    ]
    
    