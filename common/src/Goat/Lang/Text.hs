{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Goat.Lang.Text
  where

import Goat.Comp
import Goat.Prism
import Goat.Lang.Comment (spaces)
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import Data.Char (showLitChar)
import Data.String (IsString(..))
import Control.Monad.Free.Church

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

showText :: Text a -> ShowS
showText (Quote s) = showChar '"' . showLitString s . showChar '"'

fromText :: Text_ r => Text a -> r
fromText (Quote s) = quote_ s

instance Member Text Text where uprism = id

instance Member Text r => Text_ (Comp r a) where
  quote_ s = send (Quote s)
