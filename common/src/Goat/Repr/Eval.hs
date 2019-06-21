module Goat.Repr.Eval
  ( -- access wrappers
    Public(..), Local(..), Import(..)
  , Declares(..), Matches(..)
  , -- pattern
    Bindings(..), Block(..)
  , Extend(..)
  , Table(..), Assocs
  , Components(..), AnnCpts
  , Ident, showIdent
  , Trail, View
  , MonadBlock(..)
  , -- expr
    Measure(..), Repr(..), Expr(..), Value(..)
  , VarName
  , Defns, AnnDefns
  , measureRepr
  , -- preface
    Preface(..), Source
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