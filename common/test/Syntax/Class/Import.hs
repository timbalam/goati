module Syntax.Class.Import
  ( tests
  )
  where

import qualified Import (tests)
import Goat.Syntax.Import (Kr(..))
import Goat.Syntax (loadexpr, KeySource(..))

tests = Import.tests (loadexpr . flip runKr User)

    
    