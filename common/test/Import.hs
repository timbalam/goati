module Import
  ( tests
  )
  where

import qualified Syntax.Import as Import (tests)
import Goat.Eval.Dyn.Import (runFile(..), Mod(..))

tests = Import.tests (loadexpr . flip runKr User)

    
    