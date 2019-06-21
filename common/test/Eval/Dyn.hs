module Eval.Dyn (tests) where

import qualified Lang.Eval as Eval (tests)
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval.Dyn
  ( MemoRepr, DynCpts, DynError, Void
  , checkExpr
  , projectDefnError
  , Summary, summarise
  )
import Goat.Repr.Pattern (AnnCpts, Trail, View)
import Goat.Repr.Expr
  ( Value, Repr, AnnDefns
  , VarName, Ident, Import
  , measureRepr
  )
import Goat.Lang.Error (DefnError)
import Goat.Util ((<&>))
import Data.Functor (($>))
import Data.Maybe (mapMaybe)

import Debug.Trace

parses
 :: Repr
      (AnnDefns
        [View (Trail Ident)]
        [Trail Ident]
        (AnnCpts [Ident])
        Ident)
      ()
      (VarName Ident Ident (Import Ident))
 -> Either [DefnError]
      (Value
        (DynCpts DynError Ident
          (Summary (DynCpts DynError Ident) Void)))
parses m
  = case checkExpr m of
    (es, m)
     -> case mapMaybe projectDefnError es of
        []
         -> Right (fmap (summarise 0) <$> unmemo m)
        es -> Left es
  where
  memo
   :: MemoRepr Void
   -> Value (DynCpts DynError Ident (MemoRepr Void))
  memo = measureRepr
  
  unmemo
   :: Repr (DynCpts DynError Ident) () Void
   -> Value
        (DynCpts DynError Ident
          (Repr (DynCpts DynError Ident) () Void))
  unmemo m = measureRepr m

tests = Eval.tests (parses . getDefinition)
