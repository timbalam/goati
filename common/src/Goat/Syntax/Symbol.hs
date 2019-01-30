module Goat.Syntax.Symbol
  where
  
import Goat.Syntax.Comment (spaces)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import qualified Data.Text as Text


newtype Symbol = Symbol String deriving (Eq, Show)
        
parseSymbol :: String -> Parser Symbol
parseSymbol s =
  do
    xs <- Parsec.many1 (Parsec.oneOf ".+-*/^-=!?<>|&%$#~`")
    spaces
    if xs == s
      then return (Symbol xs)
      else Parsec.unexpected (showSymbol xs "")

showSymbol :: String -> ShowS
showSymbol xs = showString xs

    
{-
parseSymbol :: Symbol -> Parser ()
parseSymbol Dot =
  tryAndStripTrailingSpace (do
    Parsec.char '.'
    Parsec.notFollowedBy (Parsec.char '.')
    return ())
parseSymbol Add = stripTrailingSpace (Parsec.char '+' >> return ())
parseSymbol Sub = stripTrailingSpace (Parsec.char '-' >> return ())
parseSymbol Mul = stripTrailingSpace (Parsec.char '*' >> return ())
parseSymbol Div = stripTrailingSpace (Parsec.char '/' >> return ())
parseSymbol Pow = stripTrailingSpace (Parsec.char '^' >> return ())
parseSymbol Neg = stripTrailingSpace (Parsec.char '-' >> return ())
parseSymbol Eq = tryAndStripTrailingSpace (Parsec.string "==" >> return ())
parseSymbol Ne = tryAndStripTrailingSpace (Parsec.string "!=" >> return ())
parseSymbol Lt =
  tryAndStripTrailingSpace (do
    Parsec.char '<'
    Parsec.notFollowedBy (Parsec.char '=')
    return ())
parseSymbol Le = tryAndStripTrailingSpace (Parsec.string "<=" >> return ())
parseSymbol Gt =
  tryAndStripTrailingSpace (do
    Parsec.char '>'
    Parsec.notFollowedBy (Parsec.char '=')
    return ())
parseSymbol Ge = tryAndStripTrailingSpace (Parsec.string ">=" >> return ())
parseSymbol Or = tryAndStripTrailingSpace (Parsec.string "||" >> return ())
parseSymbol And = tryAndStripTrailingSpace (Parsec.string "&&" >> return ())
parseSymbol Not =
  tryAndStripTrailingSpace (do
    Parsec.char '!'
    Parsec.notFollowedBy (Parsec.char '=')
    return ())


tryAndStripTrailingSpace = stripTrailingSpace . Parsec.try
stripTrailingSpace = (<* spaces)

  
showSymbol :: Symbol -> ShowS
showSymbol Dot = showString "."
showSymbol Add = showChar '+'
showSymbol Sub = showChar '-'
showSymbol Mul = showChar '*'
showSymbol Div = showChar '/'
showSymbol Pow = showChar '^'
showSymbol Neg = showChar '-'
showSymbol Eq = showString "=="
showSymbol Ne = showString "!="
showSymbol Lt = showChar '<'
showSymbol Le = showString "<="
showSymbol Gt = showChar '>'
showSymbol Ge = showString ">="
showSymbol And = showString "&&"
showSymbol Or = showString "||"
showSymbol Not = showChar '!'

-}