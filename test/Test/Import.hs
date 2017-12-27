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
--import System.Directory
import Test.HUnit hiding ( Label )
import Bound hiding ( closed )
  
  
banner :: ShowMy a => a -> String
banner r = "For " ++ showMy r ++ ","


run :: ShowMy a => Expr (Sym a) -> IO (Expr (Sym a))
run =
  either throwList return . closed
  >=> runImports
  >=> either throwMy return . eval
    
    
unclosed :: (NonEmpty (ScopeError Vid) -> Assertion) -> Expr (Sym Vid) -> Assertion
unclosed f =
  either f (ioError . userError . show :: Expr (Sym Vid) -> IO ())
  . closed


fails :: Show a => (EvalError Id -> Assertion) -> Expr a -> Assertion
fails f =
  either f (ioError . userError . show)
  . eval
  
  
parses :: Syntax -> IO (Expr (Sym Vid))
parses = either throwList return . expr


scopeExpr = Closed . toScope . Member . toScope . Eval . return


tests =
  test
    [ "import" ~: let
        r = import' "./test/data/import.my"
        e = (Block [] . M.fromList) [
          (Label "test", scopeExpr (String "imported"))
          ]
        in
        parses r >>= run >>= assertEqual (banner r) e
    ]