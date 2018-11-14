module Expr.Dyn
  ( tests )
  where

import qualified Syntax.Eval as Eval (tests)
import Goat.Expr.Dyn (Synt(..), Repr, Dyn', Nec, Ident, Name, toEval, Writer, Free)
import qualified Goat.Eval.Dyn as Eval (Res, eval, Self)
import Goat.Error (StaticError, DefnError,
  eitherError, maybeDefnError)

  
  
parses
 :: Synt (Eval.Res Ident)
      (Repr Ident (Dyn' Ident)
        (Free (Repr Ident (Dyn' Ident)) (Name Ident (Nec Ident))))
 -> Either [DefnError Ident] (Eval.Self (Dyn' Ident))
parses m = eitherError maybeDefnError
  (Eval.eval (Synt (readSynt m >>= readSynt . toEval)))

tests = Eval.tests parses