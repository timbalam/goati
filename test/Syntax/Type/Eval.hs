module Syntax.Type.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Eval (K)
import My.Types.Expr (Expr, Ident, Key)
import qualified My.Types.Parser as P
import My (ScopeError, loadExpr, checkparams)
  
  
parses :: P.Expr (P.Name Ident Key P.Import) -> IO (Either [ScopeError] (Expr K a))
parses e = checkparams <$> loadExpr e []

tests = Eval.tests parses