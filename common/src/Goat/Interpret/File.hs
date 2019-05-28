{-# LANGUAGE OverloadedStrings #-}
module Goat.Interpret.File where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( tokens, parseProgBlock, progBlock, definition, parse )
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval
  ( getSelf, checkExpr
  , ImportError(..), displayImportError
  , DynError(..), Dyn, Repr, VarName, Text
  , Identity, Multi, Ident
  )
import Data.Bifunctor (bimap)
import qualified Data.Text.IO as Text
import Data.Void (Void)

-- | Load file as an expression.
runFile
  :: FilePath
  -> IO (Dyn DynError (Repr (Dyn DynError) Void))
runFile file = do
  t <- Text.readFile file
  case
    parse tokens file t
      >>= parse (progBlock definition) file of
    Left e -> fail (displayImportError (ParseError e))
    Right bs -> 
      return 
        (getSelf TypeError
          (snd
            (checkExpr 
              (getDefinition
                (parseProgBlock id bs #. "run")))))