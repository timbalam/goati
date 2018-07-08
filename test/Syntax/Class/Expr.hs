module Syntax.Class.Expr
  ( tests
  )
  where

import qualified Expr
import My.Syntax.Expr (DefnError, runE, E)
import My.Syntax.Parser (Printer, showP)
import My.Types.Expr (Expr, Nec, Ident, Key)
import qualified My.Types.Parser as P
import My.Syntax (K)
import Data.Void (Void)
  

expr
  :: E (Expr K (P.Vis (Nec Ident) Key))
  -> Either [DefnError] (Expr K (P.Name (Nec Ident) Key Void))
expr = fmap (fmap P.In) . runE
  
  
tests = Expr.tests expr
        