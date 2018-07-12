module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Eval (K)
import My.Types.Repr (Repr, Ident, Nec)
import qualified My.Types.Parser as P
import My.Syntax (ScopeError, loadexpr, applybuiltins)
import My.Syntax.Repr (BlockBuilder, E)
import qualified Data.Map as M
  
  
parses
  :: E (Repr K (P.Vis (Nec Ident) P.Key))
  -> IO (Either [ScopeError] (Repr K a))
parses e = applybuiltins M.empty <$> loadexpr (pure e) []

tests = Eval.tests parses