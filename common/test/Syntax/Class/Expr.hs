module Syntax.Class.Expr
  ( tests
  )
  where

import Data.Bifunctor
import qualified Eval (tests)
import My.Types (Repr, Ident, Nec, Assoc, eval, K, DefnError)
import My.Syntax.Repr (Check, runCheck, Name)
  
  
parses
  :: Check (Repr Assoc K Name)
  -> Either [DefnError Ident] (Repr Assoc K Name)
parses = eval . runCheck

tests = Eval.tests parses