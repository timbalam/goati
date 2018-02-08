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
import Control.Monad( (>=>) )
import Control.Exception
import Test.HUnit hiding ( Label )
import Bound( closed )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


source :: Ord a => FilePath -> Ex a -> IO (Ex a)
source = runImports
  
  
parses :: Types.Parser.Syntax -> IO (Ex a)
parses = either
  (ioError . userError . displayException . MyExceptions)
  (return . fromMaybe (error "closed") . closed)
  . getCollect . resolve Nothing . expr



tests =
  test
    [ "import" ~: let
        r = self_ "import" #. "test"
        e = String "imported" :: Ex Void
        in
        parses r >>= source "test/data" >>= assertEqual (banner r) e
        
    , "chained import" ~: let
        r = self_ "chain" #. "test"
        e = String "nested" :: Ex Void
        in
        parses r >>= source "test/data" >>= assertEqual (banner r) e
    ]