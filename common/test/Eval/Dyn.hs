module Eval.Dyn
  ( tests
  )
  where

import qualified Syntax.Eval as Eval (tests)
import Goat.Eval.Dyn (Synt, Res, Eval, Self, Dyn', eval)
import Goat.Error (DefnError, maybeDefnError, eitherError)
  
  
parses
  :: Synt (Res String) (Eval (Dyn' String))
  -> Either [DefnError String] (Self (Dyn' String))
parses m = eitherError maybeDefnError (eval m)

tests = Eval.tests parses
