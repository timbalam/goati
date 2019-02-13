module Eval.IO.Dyn
  ( tests
  )
  where

import qualified Syntax.Eval.IO as Eval (tests)
import Goat.Eval.IO.Dyn
import Goat.Error
import Goat.Eval.Dyn

parses :: Synt (Res String) (Eval (DynIO String)) -> IO ()
parses e = snd (evalIO e) >>=
  maybe (return ()) (fail . displayDynError)

tests = Eval.tests parses