module Syntax.Class.Import
  ( tests
  )
  where

import qualified Import (tests)
import My.Syntax.Import (Kr(..))
import My.Syntax (loadexpr, KeySource(..))

tests = Import.tests (loadexpr . flip runKr User)

    
    