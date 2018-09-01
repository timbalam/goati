module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Types.Repr (Repr, Ident, Nec, eval)
import qualified My.Types.Parser as P
import My.Types.Interpreter (K)
import My.Syntax.Repr (Check, runCheck, DefnError)
  
  
parses
  :: Check (Repr K (P.Vis (Nec Ident) Ident))
  -> Either [DefnError] (Repr K (P.Vis (Nec Ident) Ident))
parses = fmap eval . runCheck

tests = Eval.tests parses