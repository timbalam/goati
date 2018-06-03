module Syntax.Type.IO
  ( tests
  )
  where

import qualified IO (tests)
import My.Eval (K)
import My.Base (defaultBase)
import My.Types.Expr (Expr, Ident, Key)
import qualified My.Types.Parser as P
import My (ScopeError(..), applybase, loadExpr)
import Data.Void (Void)
  
parses :: P.Expr (P.Name Ident Key P.Import) -> IO (Either [ScopeError] (Expr K Void))
parses e = applybase defaultBase <$> loadExpr e []

tests = IO.tests parses