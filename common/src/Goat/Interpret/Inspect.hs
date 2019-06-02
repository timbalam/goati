{-# LANGUAGE FlexibleContexts, TypeFamilies, OverloadedLists, OverloadedStrings #-}
module Goat.Interpret.Inspect where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( progBlock, parseProgBlock, tokens
  , definition, toDefinition, parseDefinition
  , parse
  )
import Goat.Lang.Error (ImportError(..), displayImportError)
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval
  ( checkExpr, Repr, Multi, VarName
  , evalExpr, displaySelf
  , Identity, Text, Ident, Import
  )
import Data.Bifunctor (bimap)
import qualified Data.Text as Text


inspect :: String -> Text -> Text
inspect src t =
  Text.pack
    (either
      displayImportError
      (displaySelf . evalExpr . snd . checkExpr)
      (parseInspect src t))


-- | Load a sequence of statements

parseInspect
 :: String 
 -> Text
 -> Either ImportError
      (Repr () (Multi Identity)
        (VarName Ident Ident (Import Ident)))
parseInspect src t =
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
