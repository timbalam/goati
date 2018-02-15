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
import Types.Error
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
        r = self_ "import" #. "test"
        e = String "imported"  :: Expr K Void
        in
        runSource "test/data" r >>= assertEqual (banner r) e
        
    , "chained import" ~: let
        r = self_ "chain" #. "test"
        e = String "nested" :: Expr K Void
        in
        runSource "test/data" r >>= assertEqual (banner r) e
    ]