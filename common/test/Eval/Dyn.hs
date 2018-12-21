module Eval.Dyn
  ( tests
  )
  where

import qualified Syntax.Eval as Eval (tests)
import Goat.Eval.Dyn (Synt, Res, Eval, Self, Dyn', eval, Ident)
import Goat.Error (DefnError, maybeDefnError, eitherError)
  
  
parses
  :: Synt (Res Ident) (Eval (Dyn' Ident))
  -> Either [DefnError Ident] (Self (Dyn' Ident))
parses m = eitherError maybeDefnError (eval m)

tests = Eval.tests parses