module Eval.IO.Dyn () where

import qualified Lang.Eval.IO as Eval (tests)
{-
parses :: Synt (Res Ident) (Eval (DynIO Ident)) -> IO ()
parses e = snd (evalIO e) >>=
  maybe (return ()) (fail . displayDynError)

tests = Eval.tests parses
-}