module Syntax.Class.Eval
  ( tests
  )
  where

import qualified Eval (tests)
import My.Types.Eval (Res, Eval, Repr, Self, Dyn, eval)
import My.Types.Interpreter (K)
import My.Types.Error (StaticError(..), DefnError, Ident)
import Data.Bifunctor (first)
import Data.Maybe (mapMaybe)
  
  
parses
  :: Res Ident (Eval (Dyn Ident))
  -> Either
    [DefnError Ident]
    (Repr (Dyn Ident))
parses m = case first defnErrs (eval m) of
  ([], v) -> Right v
  (ds, _) -> Left ds
  where
    defnErrs = mapMaybe (\ e -> case e of
      DefnError de -> Just de
      _            -> Nothing)

tests = Eval.tests parses
