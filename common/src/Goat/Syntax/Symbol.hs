module Goat.Syntax.Symbol
  ( Symbol(..)
  , parseSymbol, showSymbol
  )
  where
  
import Goat.Syntax.Comment (spaces)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
  
data Symbol =
    Dot
    -- ^ A single decimal point / field accessor
  | Add
  | Sub
  | Mul
  | Div
  | Pow
  | Neg
    -- ^ Arithmetic operators
  | Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
    -- ^ Comparison operators
  | And
  | Or
  | Not
    -- ^ Logical operators
  deriving (Eq, Show)


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