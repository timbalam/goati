module Import () where

import qualified Lang.Import (tests)
{-
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
-}
--tests = Lang.Import.tests

