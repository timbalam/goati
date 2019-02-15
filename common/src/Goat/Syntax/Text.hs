{-# LANGUAGE TypeOperators, FlexibleInstances, RankNTypes #-}
module Goat.Syntax.Text
  where
  
import Goat.Co
import Goat.Syntax.Comment (spaces)
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import Data.Char (showLitChar)
import Data.String (IsString(..))

-- | Double-quote wrapped string literal
class Text_ r where
  quote_ :: String -> r

parseText :: Text_ r => Parser r
parseText =
  quote_ <$> parseTextFragment <?> "string literal"

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

-- | Concrete representation
data Text a = Quote String deriving (Eq, Show)

instance Text_ (Comp (Text <: t) a) where
  quote_ s = send (Quote s)

showText
 :: Comp (Text <: t) ShowS -> Comp t ShowS
showText = handle (\ t _ -> return (showText' t))

showText' :: Text a -> ShowS
showText' (Quote s) =
  showChar '"' . showLitString s . showChar '"'

fromText
 :: Text_ r 
 => Comp (Text <: t) r -> Comp t r
fromText = handle (\ (Quote s) _ -> return (quote_ s))

newtype SomeText =
  SomeText {
    getText :: forall t a . Comp (Text <: t) a
    }

instance Text_ SomeText where
  quote_ s = SomeText (quote_ s)

textProof :: SomeText -> SomeText
textProof = run . fromText . getText
