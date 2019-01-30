module Goat.Syntax.Keyword
  where
  
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident (Ident(..), parseIdent, showIdent)
import qualified Data.Text as Text
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)

  
newtype Keyword = Keyword Ident deriving (Eq, Show)

parseKeyword :: String -> Parser Keyword
parseKeyword s = do
  Parsec.char '@'
  Ident s' <- parseIdent
  if s' == s
    then return (Keyword (Ident s'))
    else Parsec.unexpected (showKeyword s' "")

showKeyword :: String -> ShowS
showKeyword s = showChar '@' . showString s
