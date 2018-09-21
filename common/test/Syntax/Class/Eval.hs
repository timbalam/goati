module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Types (Repr, Ident, Nec, Assoc, eval, K, DefnError)
import My.Syntax.Repr (Check, runCheck, Name)
  
  
parses
  :: Check (Repr Assoc K Name)
  -> Either [DefnError Ident] (Repr Assoc K Name)
parses = fmap eval . runCheck

tests = Eval.tests parses