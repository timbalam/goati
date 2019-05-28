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
  , Identity(..), Text, Ident, Import, ImportError(..)
  , displayImportError, displayValue
  )
import Data.Bifunctor (bimap)
import qualified Data.Text as Text


interpretProgram :: Text -> Text
interpretProgram =
  Text.pack . 
  either
    displayImportError (displayValue . snd . checkExpr) .
  parseProgram


-- | Load a sequence of statements

parseProgram
 :: Text
 -> Either ImportError
      (Repr (Multi Identity) (VarName Ident Ident (Import Ident)))
parseProgram t =
  bimap
    ParseError
    (getDefinition . 
      parseDefinition . toDefinition .
      inspectors . parseProgBlock id)
    (parse tokens "myi" t >>= parse (progBlock definition) "myi")
  where
    inspectors stmts = 
      ([ "" #. "inspect" #=
          "Define \".inspect\" and see the value here!"
      ] # stmts) #. "inspect"
