module Parser (tests) where

import qualified Lang.Parser (tests)
import Goat.Lang.Parser
  ( Parser, eof
  , CanonStmt, Void, progBlock, parseProgBlock
  , CanonExpr, definition, Self, IDENTIFIER
  )

-- Parser implementations provided via syntax class instances
rhs :: Parser (CanonExpr (Either Self IDENTIFIER))
rhs = definition

program 
 :: Parser [CanonStmt Void (CanonExpr (Either Self IDENTIFIER))]
program = parseProgBlock id <$> progBlock definition

tests = Lang.Parser.tests rhs program
