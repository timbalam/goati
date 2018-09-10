module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Types.Repr (Repr, Ident, Nec, Assoc, eval)
import qualified My.Types.Parser as P
import My.Types.Interpreter (K)
import My.Syntax.Repr (Check, runCheck, Name, DefnError)
  
  
parses
  :: Check (Repr Assoc K Name) -> Either [DefnError] (Repr Assoc K Name)
parses = fmap eval . runCheck

tests = Eval.tests parses