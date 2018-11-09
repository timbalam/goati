module Syntax.Class.IO
  ( tests
  )
  where

import qualified IO (tests)
import Goat.Eval.IO
import Goat.Types.Error
import Goat.Types.Eval

parses :: Res Ident (Eval (DynIO Ident)) -> IO ()
parses e = snd (evalIO e) >>=
  maybe (return ()) (fail . displayDynError)

tests = IO.tests parses