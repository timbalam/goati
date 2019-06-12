{-# LANGUAGE OverloadedStrings #-}
module Goat.Interpret.Run where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( tokens, parseProgBlock, progBlock
  , definition, parse
  )
import Goat.Lang.Error
  ( ImportError(..), displayImportError )
import Goat.Repr.Lang
  ( readExpr, Declared, Matched, Imported )
import Goat.Repr.Eval
  ( checkExpr, measure
  , Repr(..), TagCpts, Cpts
  , VarName, Ident, Import
  , Value, MemoRepr, DynCpts, DynError, Void
  )
import Data.Bifunctor (bimap)
import qualified Data.Text.IO as Text
import Data.Text (Text)
--import Data.Void (Void)

-- | Load file as an expression.
runFile
 :: FilePath
 -> IO (Value (DynCpts DynError (MemoRepr Void)))
runFile file
  = Text.readFile file
 >>= either
      (fail . displayImportError)
      (return . memo . snd . checkExpr)
      . parseRunFile file
  where
  memo
   :: MemoRepr Void
   -> Value (DynCpts DynError (MemoRepr Void))
  memo (Repr v) = v >>= measure


parseRunFile
 :: String
 -> Text
 -> Either ImportError
      (Repr
        (TagCpts Declared Matched (Cpts Imported))
        ()
        (VarName Ident Ident (Import Ident)))
parseRunFile src t
  = bimap
      ParseError
      (readExpr . (#. "run") . parseProgBlock id)
      (parse tokens src t
       >>= parse (progBlock definition) src)
