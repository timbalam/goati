module Syntax.Class.Repr_
  ( tests
  )
  where

import qualified Repr
import My.Syntax.Repr (DefnError, runE, E)
import My.Syntax.Parser (Printer, showP)
import My.Types.Repr (Repr, Nec, Ident)
import qualified My.Types.Parser as P
import My.Syntax (K)
import Data.Void (Void)
  

expr
  :: E (Repr K (P.Vis (Nec Ident) P.Key))
  -> Either [DefnError] (Repr K (P.Name (Nec Ident) P.Key Void))
expr = fmap (fmap P.In) . runE
  
  
tests = Repr.tests expr
        