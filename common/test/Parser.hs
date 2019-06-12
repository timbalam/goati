module Parser (tests) where

import qualified Lang.Parser (tests)
import Goat.Lang.Parser
  ( Parser, eof, whitespace
  , CanonProgStmt, progBlock, parseProgBlock
  , CanonDefinition, definition
  )
import qualified Text.Parsec as Parsec

-- Parser implementations provided via syntax class instances
rhs :: Parser CanonDefinition
rhs = definition <* eof

program
 :: Parser [CanonProgStmt CanonDefinition]
program
  = Parsec.optional whitespace
 >> parseProgBlock id <$> progBlock definition

tests = Lang.Parser.tests rhs program
