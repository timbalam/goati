module Expr.Dyn
  ( tests )
  where

import qualified Syntax.Eval as Eval (tests)
import Goat.Expr.Dyn (Synt(..), Repr, Dyn', Nec, Name, toEval, Writer, Free)
import qualified Goat.Eval.Dyn as Eval (Res, eval, Self)
import Goat.Error (StaticError, DefnError,
  eitherError, maybeDefnError)

  
  
parses
 :: Synt (Eval.Res String)
      (Repr
        String
        (Dyn' String)
        (Free
          (Repr String (Dyn' String))
          (Name String (Nec String))))
 -> Either [DefnError String] (Eval.Self (Dyn' String))
parses m = eitherError maybeDefnError
  (Eval.eval (Synt (readSynt m >>= readSynt . toEval)))

tests = Eval.tests parses