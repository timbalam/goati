module Goat.Syntax.Prec
  ( Op(..)
  , parsePoint, showPoint
  , parseAdd, parseSub, parseMul, parseDiv, parsePow
  , parseEq, parseNe, parseLt, parseLe, parseGt, parseGe
  , showAdd, showSub, showMul, showDiv, showPow
  , showEq, showNe, showLt, showLe, showGt, showGe
  , Precedence(..)
  , prec, preceeds, doesNotPreceed
  )
  where
  
import Goat.Syntax.Comment (spaces)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
  
data Op =
    Point
  | Add
  | Sub
  | Mul
  | Div
  | Pow
  | Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge


parsePoint, parseAdd, parseSub, parseMul, parseDiv, parseEq, parseNe,
  parseLt, parseLe, parseGt, parseGe :: Parser Op
  
showPoint, showAdd, showSub, showMul, showDiv, showEq, showNe,
  showLt, showLe, showGt, showGe :: ShowS

-- | A single decimal point / field accessor
parsePoint =
  tryAndStripTrailingSpace (do
    Parsec.char '.'
    Parsec.notFollowedBy (Parsec.char '.')
    return Point)
    
showPoint = showString "."
    
-- | Arithmetic operators
parseAdd = stripTrailingSpace (Parsec.char '+' >> return Add)
parseSub = stripTrailingSpace (Parsec.char '-' >> return Sub)
parseMul = stripTrailingSpace (Parsec.char '*' >> return Mul)
parseDiv = stripTrailingSpace (Parsec.char '/' >> return Div)
parsePow = stripTrailingSpace (Parsec.char '^' >> return Pow)

showAdd = showChar '+'
showSub = showChar '-'
showMul = showChar '*'
showDiv = showChar '/'
showPow = showChar '^'

-- | Comparison operators
parseEq = tryAndStripTrailingSpace (Parsec.string "==" >> return Eq)
parseNe = tryAndStripTrailingSpace (Parsec.string "!=" >> return Ne)
parseLt =
  tryAndStripTrailingSpace (do
    Parsec.char '<'
    Parsec.notFollowedBy (Parsec.char '=')
    return Lt)
parseLe = Parsec.try (Parsec.string "<=" >> return Le) <* spaces
parseGt =
  tryAndStripTrailingSpace (do
    Parsec.char '>'
    Parsec.notFollowedBy (Parsec.char '=')
    return Gt)
parseGe = tryAndStripTrailingSpace (Parsec.string ">=" >> return Ge)

showEq = showString "=="
showNe = showString "!="
showLt = showChar '<'
showLe = showString "<="
showGt = showChar '>'
showGe = showString ">="

tryAndStripTrailingSpace = stripTrailingSpace . Parsec.try
stripTrailingSpace = (<* spaces)


data Precedence =
    LeftAssoc
  | RightAssoc
  | NoAssoc


-- | a `prec` b returns a 'Precedence' type deciding whether
-- a associates with unambiguously higher precedence than b.
prec :: Op -> Op -> Precedence
prec Point _     = LeftAssoc
prec _     Point = RightAssoc
prec Pow   Pow   = LeftAssoc
prec Pow   Mul   = LeftAssoc
prec Pow   Div   = LeftAssoc
prec Pow   Add   = LeftAssoc
prec Pow   Sub   = LeftAssoc
prec Mul   Pow   = RightAssoc
prec Div   Pow   = RightAssoc
prec Add   Pow   = RightAssoc
prec Sub   Pow   = RightAssoc
prec Mul   Mul   = LeftAssoc
prec Mul   Div   = LeftAssoc
prec Mul   Add   = LeftAssoc
prec Mul   Sub   = LeftAssoc
prec Div   Mul   = LeftAssoc
prec Div   Div   = LeftAssoc
prec Div   Add   = LeftAssoc
prec Div   Sub   = LeftAssoc
prec Add   Mul   = RightAssoc
prec Sub   Mul   = RightAssoc
prec Add   Div   = RightAssoc
prec Sub   Div   = RightAssoc
prec Add   Add   = LeftAssoc
prec Add   Sub   = LeftAssoc
prec Sub   Add   = LeftAssoc
prec Sub   Sub   = LeftAssoc
prec _     _     = NoAssoc


preceeds :: Op -> Op -> Bool
preceeds a b = case a `prec` b of 
  LeftAssoc -> True
  _         -> False

doesNotPreceed :: Op -> Op -> Bool
doesNotPreceed a b = not (preceeds a b)