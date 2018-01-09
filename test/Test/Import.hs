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
run =
  runImports
  >=> either throwMy return . eval
    
    
unclosed :: (NonEmpty (ScopeError Vid) -> Assertion) -> Expr Vid -> Assertion
unclosed f =
  either f (ioError . userError . show :: Expr Vid -> IO ())
  . closed


fails :: Show a => (EvalError Id -> Assertion) -> Expr a -> Assertion
fails f =
  either f (ioError . userError . show)
  . eval
  
  
parses :: Syntax -> IO (Expr Vid)
parses = either throwList return . expr


scopeExpr = Closed . toScope . Member . toScope


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