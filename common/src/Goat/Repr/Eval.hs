module Goat.Repr.Eval
  ( -- access wrappers
    Public(..), Local(..), Import(..)
  , Tag(..), Declares(..), Matches(..)
  , -- pattern
    Bindings(..), Block(..)
  , Extend(..)
  , Assocs(..), Assocs', AnnCpts
  , Ident, showIdent
  , MonadBlock(..)
  , -- expr
    Measure(..), Repr(..), Expr(..), Value(..)
  , VarName
  , Defns
  , measureRepr
  , -- preface
    Preface(..), Imports, Source
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