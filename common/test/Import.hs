module Import
  ( tests
  )
  where

import qualified Syntax.Import as Import (tests)
import Goat.Eval.Dyn.Import (runFile(..))
import Goat.Syntax (loadexpr, KeySource(..))

tests = Import.tests (loadexpr . flip runKr User)

    
    