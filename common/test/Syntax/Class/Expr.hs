module Syntax.Class.Expr
  ( tests
  )
  where

import Control.Monad.Writer
import qualified Eval (tests)
import My.Types.Expr (Repr, Dyn, Ident, Name, toEval)
import qualified My.Types.Eval as Eval (eval, Self)
import My.Types.Error (StaticError, DefnError,
  eitherError, maybeDefnError)
  
  
parses
  :: Writer [StaticError Ident] (Repr Ident (Dyn Ident) Name)
  -> Either [DefnError Ident] (Eval.Self (Dyn Ident))
parses m = eitherError maybeDefnError
  (Eval.eval (lift m >>= toEval))

tests = Eval.tests parses