module Parser (tests) where

import qualified Lang.Parser (tests)
import Goat.Lang.Parser
  ( Parser, eof, whitespace
  , CanonStmt, Void, progBlock, parseProgBlock
  , CanonExpr, definition, Self, IDENTIFIER
  )
import qualified Text.Parsec as Parsec

-- Parser implementations provided via syntax class instances
rhs :: Parser (CanonExpr (Either Self IDENTIFIER))
rhs = definition <* eof

program
 :: Parser [CanonStmt Void (CanonExpr (Either Self IDENTIFIER))]
program =
  Parsec.optional whitespace >>
    parseProgBlock id <$> progBlock definition

tests = Lang.Parser.tests rhs program
