module Syntax.Class.IO
  ( tests
  )
  where

import qualified IO (tests)
import My.Eval (K)
import My.Base (defaultBase)
import My.Types.Expr (Expr, Ident, Nec, Key)
import qualified My.Types.Parser as P
import My.Syntax (ScopeError(..), applybase, loadexpr)
import My.Syntax.Expr (E)
import Data.Void (Void)
  
parses :: E (Expr K (P.Vis (Nec Ident) Key)) -> IO (Either [ScopeError] (Expr K Void))
parses e = applybase defaultBase <$> loadexpr (pure e) []

tests = IO.tests parses