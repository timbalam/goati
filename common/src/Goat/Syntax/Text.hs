module Goat.Syntax.Text
  where
  
import Goat.Syntax.Comment (spaces)
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import Data.Char (showLitChar)
import Data.String (IsString(..))


newtype Text = Text String

class Text_ r where
  quote_ :: String -> r
  
instance Text_ Text where
  quote_ = Text

-- | Parse a double-quote wrapped string literal
parseText :: Text_ r => Parser r
parseText =
  quote_ <$> parseTextFragment <?> "string literal"

showText :: Text -> ShowS
showText (Text s) = showChar '"' . showLitString s . showChar '"'

fromText :: Text_ r => Text -> r
fromText (Text s) = quote_ s

-- | Parse a double-quote wrapped string literal
parseTextFragment :: Parser String
parseTextFragment =
  Parsec.between
    (Parsec.char '"')
    (Parsec.char '"' >> spaces)
    (Parsec.many (Parsec.noneOf "\"\\" <|> escapedchars))

    
-- | Parse an escaped character
escapedchars :: Parser Char
escapedchars =
  do
    Parsec.char '\\'
    x <- Parsec.oneOf "\\\"nrt"
    return
      (case x of
        '\\' ->
          x
          
        '"'  ->
          x
          
        'n'  ->
          '\n'
      
        'r'  ->
          '\r'
        
        't'  ->
          '\t')


showLitString :: String -> ShowS
showLitString []          s = s
showLitString ('"' : cs)  s =  "\\\"" ++ (showLitString cs s)
showLitString (c   : cs)  s = showLitChar c (showLitString cs s)
