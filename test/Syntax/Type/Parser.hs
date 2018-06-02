module Syntax.Type.Parser 
  ( tests
  ) where

import qualified Parser
import My.Types.Parser (Program, Expr, Name, Ident, Key, Import)
import qualified My.Parser
  

-- Parser implementations provided by 'ReadMy' class instances
rhs :: My.Parser.Parser (Expr (Name Ident Key Import))
rhs = My.Parser.readsMy

program :: My.Parser.Parser (Program Import)
program = My.Parser.readsMy


tests = Parser.tests rhs program