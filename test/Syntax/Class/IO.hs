module Syntax.Class.IO
  ( tests
  )
  where

import qualified IO (tests)
import My.Eval (K)
import My.Builtin (builtins)
import My.Types.Repr (Repr, Ident, Nec)
import qualified My.Types.Parser as P
import My.Syntax (ScopeError(..), applybuiltins, loadexpr)
import My.Syntax.Repr (E)
import Data.Void (Void)
  
parses
  :: E (Repr K (P.Vis (Nec Ident) P.Key))
  -> IO (Either [ScopeError] (Repr K Void))
parses e = applybuiltins builtins <$> loadexpr (pure e) []

tests = IO.tests parses