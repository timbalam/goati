module Eval.Dyn (tests) where

import qualified Lang.Eval as Eval (tests)
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval.Dyn
  ( MemoRepr, DynCpts, DynError, Void
  , checkExpr
  , projectDefnError
  , Summary, summarise
  )
import Goat.Repr.Expr
  ( Value, Repr, AmbigCpts
  , VarName, Ident, Import
  , measureRepr
  )
import Goat.Lang.Error (DefnError)
import Goat.Util ((<&>))
import Data.Functor (($>))
import Data.Maybe (mapMaybe)

import Debug.Trace

parses
 :: Repr AmbigCpts ()
      (VarName Ident Ident (Import Ident))
 -> Either [DefnError]
      (Value
        (DynCpts DynError
          (Summary (DynCpts DynError) Void)))
parses m
  = case checkExpr m of
    (es, m)
     -> case mapMaybe projectDefnError es of
        []
         -> Right (fmap (summarise 2) <$> unmemo m)
        es -> Left es
  where
  memo
   :: MemoRepr Void
   -> Value (DynCpts DynError (MemoRepr Void))
  memo = measureRepr
  
  unmemo
   :: Repr (DynCpts DynError) () Void
   -> Value
        (DynCpts DynError
          (Repr (DynCpts DynError) () Void))
  unmemo m = measureRepr m

tests = Eval.tests (parses . getDefinition)
