module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Eval (K)
import My.Types.Expr (Expr, Ident, Nec)
import qualified My.Types.Parser as P
import My.Syntax (ScopeError, loadexpr, applybuiltins)
import My.Syntax.Expr (BlockBuilder, E)
import qualified Data.Map as M
  
  
parses
  :: E (Expr K (P.Vis (Nec Ident) P.Key))
  -> IO (Either [ScopeError] (Expr K a))
parses e = applybuiltins M.empty <$> loadexpr (pure e) []

tests = Eval.tests parses