module Import
  ( tests
  )
  where

import qualified Syntax.Import as Import (tests)
import Goat.Syntax.Import (Kr(..))
import Goat.Syntax (loadexpr, KeySource(..))

tests = Import.tests (loadexpr . flip runKr User)

    
    