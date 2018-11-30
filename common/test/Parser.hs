module Parser 
  ( tests
  ) where

import qualified Syntax.Parser (tests)
import Goat.Syntax.Syntax (Program, Expr, Name, Ident, Key)
import Goat.Syntax.Parser
import qualified Text.Parsec as P (eof)

-- Parser implementations provided via syntax class instances
rhs :: Parser (Expr (Name Key Ident))
rhs = syntax <* P.eof

tests = Syntax.Parser.tests rhs (program' :: Parser Program)
