module Eval.Dyn (tests) where

import qualified Lang.Eval as Eval (tests)
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval.Dyn
  ( MemoRepr, Dyn, DynError, Void, checkExpr, evalExpr
  , projectDefnError
  )
import Goat.Repr.Expr
  ( Value, Repr, Multi, Identity, VarName, Ident, Import )
import Goat.Lang.Error (DefnError)
import Data.Functor (($>))
import Data.Maybe (mapMaybe)

data NA = NA deriving Show
instance Eq NA where _ == _ = False
 
parses
  :: Repr () (Multi Identity) (VarName Ident Ident (Import Ident))
  -> Either [DefnError] (Value NA)
parses m =
  case checkExpr m of
    (es, v) -> case mapMaybe projectDefnError es of
      [] -> Right (evalExpr v $> NA)
      es -> Left es

tests = Eval.tests (parses . getDefinition)
