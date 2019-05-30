module Goat.Repr.Eval
  ( -- access wrappers
    Public(..), Local(..), Import(..)
  , -- pattern
    Bindings(..), Match(..), Abs(..)
  , Bind, Block
  , Components(..), Extend(..), Identity(..), Map, Text
  , Decompose, Multi
  , Ident, showIdent
  , MonadBlock(..)
  , -- expr
    Repr(..), Expr(..), VarName
  , -- preface
    Preface(..), Imports, Module, Source
  , -- dyn
    Dyn, mapError
  , -- eval
    Self, MemoRepr, getSelf, checkExpr, eval
  , -- error
    DynError(..), StaticError(..)
    -- printing
  , displayValue, displayDyn
  , displayDynError, displayStaticError, displayErrorList
  )
  where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.Preface
import Goat.Repr.Dyn
import Goat.Repr.Eval.Dyn
import Goat.Error