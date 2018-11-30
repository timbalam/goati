module Import
  ( tests
  )
  where

import qualified Syntax.Import as Import (tests)
import Goat.Syntax.Class
import Goat.Error
import Goat.Eval.Dyn
import Goat.Eval.Dyn.Import

apply
 :: Include Ident (Dyn' Ident)
 -> [(Ident, Include Ident (Dyn' Ident))]
 -> Include Ident (Dyn' Ident)
apply (Include inc) mods =
  Include (applyImports
      (map fst ps)
      (map (getInclude . snd) ps)
      inc)

mod
  :: Include Ident (Dyn' Ident)
  -> Either [StaticError Ident] (Repr (Dyn' Ident))
mod (Include resmod) = case evalImport resmod of
  ([], m) -> Right (m #. "run")
  (es, _) -> Left es

tests = Import.tests apply mod

