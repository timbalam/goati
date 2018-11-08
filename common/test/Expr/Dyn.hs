module Expr.Dyn
  ( tests )
  where

import qualified Syntax.Eval as Eval (tests)
import Goat.Expr.Dyn (Repr, Dyn', Ident, Name, toEval)
import qualified Goat.Eval.Dyn as Eval (eval, Self)
import Goat.Error (StaticError, DefnError,
  eitherError, maybeDefnError)
import Control.Monad.Writer
  
  
parses
  :: Writer [StaticError Ident] (Repr Ident (Dyn' Ident) Name)
  -> Either [DefnError Ident] (Eval.Self (Dyn' Ident))
parses m = eitherError maybeDefnError
  (Eval.eval (lift m >>= toEval))

tests = Eval.tests parses