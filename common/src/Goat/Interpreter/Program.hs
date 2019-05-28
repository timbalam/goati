{-# LANGUAGE FlexibleContexts, TypeFamilies, OverloadedLists, OverloadedStrings #-}
module Goat.Interpreter.Program where


import Goat.Lang.Class
import Goat.Lang.Parser
  ( progBlock, parseProgBlock, tokens
  , definition, toDefinition, parseDefinition )
import Goat.Repr.Lang.Expr (getDefinition)
import Goat.Repr.Expr
import Goat.Repr.Eval.Dyn
import Goat.Repr.Pattern (Identity, Multi, Ident)
import Data.Bifunctor (bimap)
import qualified Data.Text as Text
import Text.Parsec (parse)


interpret :: Text -> Text
interpret =
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
