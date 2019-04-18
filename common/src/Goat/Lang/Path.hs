{-# LANGUAGE TypeOperators, ConstraintKinds, FlexibleContexts, TypeFamilies #-}
module Goat.Lang.Path
  where

import Goat.Comp
import Goat.Lang.Field
import Goat.Lang.Ident
import Goat.Lang.Reflect
import Data.Functor.Identity (Identity(..))
import Data.Void (Void)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
  

