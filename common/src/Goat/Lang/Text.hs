{-# LANGUAGE TypeOperators, FlexibleInstances, FlexibleContexts, RankNTypes #-}
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
data Text = Quote String deriving (Eq, Show)

showText :: Text -> ShowS
showText (Quote s) = showChar '"' . showLitString s . showChar '"'

fromText :: Text_ r => Text -> r
fromText (Quote s) = quote_ s

class UText r where utext :: Prism' (r a) Text

instance (Functor r, UText r) => Text_ (F r a) where
  quote_ s = wrap (review utext (Quote s))

{-  
-- instance Member Text r => Text_ (Comp r a) where
--  quote_ s = send (Quote s)

showTextM
 :: F (Const Text) ShowS -> F t ShowS
showTextM = handle (\ t _ -> return (showText' t))


fromText
 :: Text_ r 
 => Comp (Text <: t) r -> Comp t r
fromText = handle (\ (Quote s) _ -> return (quote_ s))
-}
