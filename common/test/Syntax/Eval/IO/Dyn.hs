module Syntax.Eval.IO.Dyn
  ( tests
  )
  where

import qualified Eval.IO (tests)
import Goat.Eval.IO.Dyn
import Goat.Error
import Goat.Eval.Dyn

parses :: Res Ident (Eval (DynIO Ident)) -> IO ()
parses e = snd (evalIO e) >>=
  maybe (return ()) (fail . displayDynError)

tests = Eval.IO.tests parses