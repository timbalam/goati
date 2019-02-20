module Goat.Lang.Keyword
  where
  
import Goat.Lang.Comment (spaces)
import Goat.Lang.Ident (parseIdentEnd)
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)

parseKeyword :: String -> Parser String
parseKeyword s = do
  Parsec.char '@'
  s <- Parsec.string s
  parseIdentEnd
  spaces
  return s

showKeyword :: String -> ShowS
showKeyword s = showChar '@' . showString s
