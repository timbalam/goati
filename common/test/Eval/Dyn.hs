module Eval.Dyn (tests) where

import qualified Lang.Eval as Eval (tests)
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval.Dyn
  ( Dyn, DynError, Void, checkExpr, eval )
import Goat.Repr.Expr
  ( Repr, Multi, Identity, VarName, Ident, Import )
import Goat.Error (DefnError, projectDefnError)
import Data.Maybe (mapMaybe)

  
parses
  :: Repr (Multi Identity) (VarName Ident Ident (Import Ident))
  -> Either [DefnError] (Repr (Dyn DynError) Void)
parses m =
  case checkExpr m of
    (es, v) -> case mapMaybe projectDefnError es of
      [] -> Right (eval v)
      es -> Left es

tests = Eval.tests (parses . getDefinition)
