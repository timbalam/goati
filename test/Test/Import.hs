{-# LANGUAGE OverloadedStrings #-}
module Test.Import
  ( tests
  )
  where

import Expr
import Eval
import Types.Expr
import Types.Classes
import Types.Parser.Short
import qualified Types.Parser as Parser
import Types.Error
import Lib

import Data.List.NonEmpty( NonEmpty )
import Data.Foldable( asum )
import qualified Data.Map as M
import Control.Monad( (>=>) )
import Control.Exception
import Test.HUnit hiding ( Label )
import Bound hiding ( closed )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


source :: Ord a => FilePath -> Expr ListO (Key Parser.Symbol) Parser.Var -> IO (Expr M.Map (Key a) b)
source src =
  either (ioError . userError . displayException . MyExceptions) (runImports src) . closed
    
    
unclosed :: (NonEmpty ScopeError -> Assertion) -> Expr ListO (Key Parser.Symbol) Parser.Var -> Assertion
unclosed f =
  either f (ioError . userError . show :: Ex_ -> IO ())
  . closed
  
  
parses :: Parser.Syntax_ -> IO (Expr ListO (Key Parser.Symbol) Parser.Var)
parses = either (ioError . userError . displayException . MyExceptions) return . symexpr "<test>@"


tests =
  test
    [ "import" ~: let
        r = env_ "import" #. "test"
        e = String "imported" :: Ex_
        in
        parses r >>= source "test/data" >>= assertEqual (banner r) e
        
    , "chained import" ~: let
        r = env_ "chain" #. "chain" #. "test"
        e = String "imported" :: Ex_
        in
        parses r >>= source "test/data" >>= assertEqual (banner r) e
        
    , "chained import from nested file" ~: let
        r = env_ "chain" #. "chainNested" #. "test"
        e = String "imported" :: Ex_
        in
        parses r >>= source "test/data/nested" >>= assertEqual (banner r) e
    ]