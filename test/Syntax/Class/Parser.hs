module Syntax.Class.Parser 
  ( tests
  ) where

import qualified Parser (tests)
import My.Types.Parser (Program, Expr, Name, Ident, Key, Import)
import qualified My.Syntax.Parser
import qualified Text.Parsec

-- Parser implementations provided via syntax class instances
rhs :: My.Syntax.Parser.Parser (Expr (Name Ident Key Import))
rhs = My.Syntax.Parser.syntax <* Text.Parsec.eof

program :: My.Syntax.Parser.Parser (Program Import)
program = My.Syntax.Parser.program

tests = Parser.tests rhs program
