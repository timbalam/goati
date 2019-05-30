{-# LANGUAGE FlexibleContexts, TypeFamilies, OverloadedLists, OverloadedStrings #-}
module Goat.Interpret.Program where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( progBlock, parseProgBlock, tokens
  , definition, toDefinition, parseDefinition
  , parse
  )
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval
  ( checkExpr, Repr, Multi, VarName
  , Identity, Text, Ident, Import, displayValue
  )
import Goat.Error (ImportError(..), displayImportError)
import Data.Bifunctor (bimap)
import qualified Data.Text as Text


interpretProgram :: String -> Text -> Text
interpretProgram src t =
  Text.pack
    (either
      displayImportError
      (displayValue . snd . checkExpr)
      (parseProgram src t))


-- | Load a sequence of statements

parseProgram
 :: String 
 -> Text
 -> Either ImportError
      (Repr () (Multi Identity)
        (VarName Ident Ident (Import Ident)))
parseProgram src t =
  bimap
    ParseError
    (getDefinition . 
      parseDefinition . toDefinition .
      inspectors . parseProgBlock id)
    (parse tokens src t >>= parse (progBlock definition) src)
  where
    inspectors stmts = 
      [ "" #. "inspect" #=
          "Define \".inspect\" and see the value here!"
      ] # stmts #. "inspect"
