module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Eval (K)
import My.Types.Expr (Expr, Ident, Nec, Key)
import qualified My.Types.Parser as P
import My.Syntax (ScopeError, loadexpr, applybase)
import My.Syntax.Expr (BlockBuilder, E)
import qualified Data.Map as M
  
  
parses
  :: E (Expr K (P.Vis (Nec Ident) Key))
  -> IO (Either [ScopeError] (Expr K a))
parses e = applybase M.empty <$> loadexpr (pure e) []

tests = Eval.tests parses