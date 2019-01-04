module Goat.Syntax.Keyword
  where
  
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident (Ident, parseIdent, showIdent)
import Data.String (IsString(..))
import qualified Data.Text as Text
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)

  
data Keyword = Keyword Ident deriving (Eq, Show)

instance IsString Keyword where
  fromString s = case result of
      Left err -> error (show err)
      Right i  -> i
    where
      result = Parsec.parse
        (parseKeyword <* Parsec.eof)
        ""
        (Text.pack s)

parseKeyword :: Parser Keyword
parseKeyword = do
  Parsec.char '@'
  i <- parseIdent
  return (Keyword i)
  
showKeyword :: Keyword -> ShowS
showKeyword (Keyword i) = showChar '@' . showIdent i

parseKeywordIdent :: Ident -> Parser Ident
parseKeywordIdent s = do
  Keyword k <- parseKeyword
  if k == s
    then return k
    else Parsec.unexpected (showIdent s "")
    

showKeywordIdent :: Ident -> ShowS
showKeywordIdent s = showKeyword (Keyword s)