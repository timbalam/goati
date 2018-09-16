module Syntax.Class.Parser 
  ( tests
  ) where

import qualified Parser (tests)
import My.Types.Syntax (Program, Expr, Name, Ident, Key, Import)
import My.Syntax.Parser
import qualified Text.Parsec as P (eof)

-- Parser implementations provided via syntax class instances
rhs :: Parser (Expr (Name Ident Key Import))
rhs = syntax <* P.eof

tests = Parser.tests rhs (program' :: Parser (Program Import))
