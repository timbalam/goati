module Goat.Syntax.Keyword
  where
  
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident (Ident(..), parseIdent, showIdent)
import qualified Data.Text as Text
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)

parseKeyword :: String -> Parser String
parseKeyword s = do
  Parsec.char '@'
  s' <- parseIdent
  if s' == s
    then return s'
    else Parsec.unexpected (showKeyword s' "")

showKeyword :: String -> ShowS
showKeyword s = showChar '@' . showString s
