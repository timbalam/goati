module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Types.Eval (Res, Eval, Self, Dyn', eval, Ident)
import My.Types.Error (DefnError, maybeDefnError, eitherError)
  
  
parses
  :: Res Ident (Eval (Dyn' Ident))
  -> Either [DefnError Ident] (Self (Dyn' Ident))
parses m = eitherError maybeDefnError (eval m)

tests = Eval.tests parses
