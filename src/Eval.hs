{-# LANGUAGE FlexibleContexts #-}

module Eval
  ( evalRval
  , browse
  , loadProgram
  , readProgram
  , readValue
  , primitiveBindings
  )
where
import Eval.Value
import Eval.IO

type Getter s a = (s -> a)
type Setter s t a b = (a -> b) -> s -> t
type Setter' s a = Setter s s a a
        