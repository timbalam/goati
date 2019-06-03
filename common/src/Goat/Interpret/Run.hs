{-# LANGUAGE OverloadedStrings #-}
module Goat.Interpret.Run where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( tokens, parseProgBlock, progBlock, definition, parse )
import Goat.Lang.Error (ImportError(..), displayImportError)
import Goat.Repr.Lang (readExpr)
import Goat.Repr.Eval
  ( checkExpr, measure
  , Repr, Multi, Identity
  , VarName, Ident, Import
  , Value, MemoRepr, DynError, Dyn, Void
  )
import Data.Bifunctor (bimap)
import qualified Data.Text.IO as Text
import Data.Text (Text)
--import Data.Void (Void)

-- | Load file as an expression.
runFile
 :: FilePath
 -> IO (Value (Dyn DynError (MemoRepr (Dyn DynError) Void)))
runFile file =
  Text.readFile file >>=
    either
      (fail . displayImportError)
      (return . memo . snd . checkExpr) .
      parseRunFile file
  where
    memo
     :: MemoRepr (Dyn DynError) Void
     -> Value (Dyn DynError (MemoRepr (Dyn DynError) Void))
    memo = measure


parseRunFile
 :: String
 -> Text
 -> Either ImportError
      (Repr () (Multi Identity)
        (VarName Ident Ident (Import Ident)))
parseRunFile src t =
  bimap
    ParseError
    (readExpr . (#. "run") . parseProgBlock id)
    (parse tokens src t >>= parse (progBlock definition) src)
