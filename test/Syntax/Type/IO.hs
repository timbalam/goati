module Syntax.Type.IO
  ( tests
  )
  where

import qualified IO (tests)
import My.Eval (K)
import My.Builtin (builtins)
import My.Types.Expr (Expr, Ident, Key)
import qualified My.Types.Parser as P
import My (ScopeError(..), applybuiltins, loadExpr)
import Data.Void (Void)
  
parses :: P.Expr (P.Name Ident Key P.Import) -> IO (Either [ScopeError] (Expr K Void))
parses e = applybuiltins builtins <$> loadExpr e []

tests = IO.tests parses