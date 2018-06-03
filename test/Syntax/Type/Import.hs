module Syntax.Type.Import
  ( tests
  )
  where

import qualified Import (tests)
import My (loadExpr)
  

tests = Import.tests loadExpr

    