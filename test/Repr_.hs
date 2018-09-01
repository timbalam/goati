{-# LANGUAGE OverloadedStrings, RankNTypes, FlexibleContexts, TypeFamilies #-}

module Repr
  ( tests
  )
  where

import My.Syntax.Parser (Printer, showP)
import My.Syntax.Repr (DefnError(..))
import qualified My.Types.Parser as P
import My.Types.Repr
import My.Syntax.Interpreter (K, MyException(..))
import My.Types.Syntax.Class
import Data.String (IsString)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Exception
import Test.HUnit
  
banner :: Printer -> String
banner r = "For " ++ showP r ","


parses
  :: (Eq a, Show a)
  => Either [DefnError] (Repr K (P.Name (Nec Ident) P.Key a))
  -> IO (Repr K (P.Name (Nec Ident) P.Key a))
parses = either
  (ioError . userError . displayException
    . MyExceptions :: [DefnError] -> IO a)
  return
  
  
fails
  :: (Eq a, Show a)
  => ([DefnError] -> Assertion)
  -> Either [DefnError] (Repr K (P.Name (Nec Ident) P.Key a))
  -> Assertion
fails f = either f
  (ioError . userError . shows "Unexpected: " . show)
  
  
tests
  :: (Expr a, Eq b, Show b)
  => (a -> Either [DefnError] (Repr K (P.Name (Nec Ident) P.Key b)))
  -> Test
tests expr =
  test
    [ 
       
    ]
        