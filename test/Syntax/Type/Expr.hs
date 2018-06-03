{-# LANGUAGE OverloadedStrings #-}

module Syntax.Type.Expr
  ( tests
  )
  where

import qualified Expr
import My.Expr (DefnError, expr)
import My.Types.Expr (Expr, Nec, Ident, Key)
import qualified My.Types.Parser as P
import My (K)

type E =
  P.Expr (P.Name Ident Key P.Import)
    -> Either [DefnError] (Expr K (P.Name (Nec Ident) Key P.Import))
  
tests = Expr.tests (expr :: E)
        