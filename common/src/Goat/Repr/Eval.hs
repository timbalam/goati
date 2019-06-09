module Goat.Repr.Eval
  ( -- access wrappers
    Public(..), Local(..), Import(..)
  , -- pattern
    Bindings(..), Block(..), BlockCpts
  , Extend(..), Map, Text
  , AmbigCpts
  , Ident, showIdent
  , MonadBlock(..)
  , -- expr
    Measure(..), Repr(..), Expr(..), Value(..)
  , VarName
  , TagCpts, CptIn
  , measureRepr
  , -- preface
    Preface(..), AmbigImports, Module, Source
  , CptEx
  , -- dyn
    DynCpts, mapError
  , -- eval
    MemoRepr, eval, checkExpr, Void
  , -- error
    DynError(..), StaticError(..)
    -- printing
  , displayExpr, displayDynCpts
  , displayDynError, displayStaticError
  , displayErrorList
  )
  where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.Preface
import Goat.Repr.Dyn
import Goat.Repr.Eval.Dyn
import Goat.Lang.Error (displayErrorList)