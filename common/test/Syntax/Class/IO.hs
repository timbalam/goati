module Syntax.Class.IO
  ( tests
  )
  where

import qualified IO (tests)
import My.Eval.IO
import My.Types.Error
import My.Types.Eval

parses :: Res Ident (Eval (DynIO Ident)) -> IO ()
parses e = snd (evalIO e) >>=
  maybe (return ()) (fail . displayDynError)

tests = IO.tests parses