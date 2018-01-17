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
import Types.Parser( Syntax )
import Types.Error
import Lib

import Data.List.NonEmpty( NonEmpty )
import Data.Foldable( asum )
import qualified Data.Map as M
import Control.Monad( (>=>) )
import Test.HUnit hiding ( Label )
import Bound hiding ( closed )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: Expr Vid -> IO (Expr Vid)
run = runImports >=> eval
    
    
unclosed :: (NonEmpty (ScopeError Vid) -> Assertion) -> Expr Vid -> Assertion
unclosed f =
  either f (ioError . userError . show :: Expr Vid -> IO ())
  . closed
  
  
parses :: Syntax -> IO (Expr Vid)
parses = either throwList return . expr


tests =
  test
    [ "import" ~: let
        r = env_ "test/data/import" #. "test"
        e = String "imported"
        in
        parses r >>= run >>= assertEqual (banner r) e
        
    , "chained import" ~: let
        r = env_ "test/data/chain" #. "chain" #. "test"
        e = String "imported"
        in
        parses r >>= run >>= assertEqual (banner r) e
        
    , "chained import from nested file" ~: let
        r = env_ "test/data/nested/chain" #. "chainNested" #. "test"
        e = String "imported"
        in
        parses r >>= run >>= assertEqual (banner r) e
    ]