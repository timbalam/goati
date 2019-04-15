module Goat.Lang.Symbol
  where

import Goat.Lang.Comment (spaces)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import qualified Data.Text as Text

--import Debug.Trace (trace)

        
parseSymbol :: String -> Parser String
parseSymbol s =
  Parsec.try 
    (Parsec.string s <* parseSymbolEnd)
    <* spaces

parseSymbolEnd :: Parser ()
parseSymbolEnd =
  Parsec.notFollowedBy (Parsec.oneOf ".+-*/^-=!?<>|&%$#~`")

showSymbol :: String -> ShowS
showSymbol xs = showString xs

showPad :: String -> ShowS -> ShowS -> ShowS
showPad s a b = a . showChar ' ' . showSymbol s . showChar ' ' . b