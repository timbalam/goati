module Prec
  where
  
import Goat.Syntax.Comment (spaces)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
  
data Op =
    PointOp


-- | A single decimal point / field accessor
parsePoint :: Parser Op
parsePoint =
  Parsec.try (do
    Parsec.char '.'
    Parsec.notFollowedBy (Parsec.char '.')
    return Point)
    <* spaces
    
showOp :: Op -> ShowS
showOp PointOp = showString "."



data Precedence =
    LeftAssoc
  | RightAssoc
  | NoAssoc


-- | a `prec` b returns a 'Precedence' type deciding whether
-- a associates with unambiguously higher precedence than b.
prec :: Op -> Op -> Precedence
prec PointOp _ = LeftAssoc


parseOp :: (Op -> Precedence) -> Parser a
parseOp f p = 




  i <- parseIdent
  return (#. i))

showField
  :: ((Op -> Precedence) -> a -> ShowS)
  -> (Op -> Precedence) -> Field a -> ShowS
showField showa p (a :#. i) =
  showParen (p PointOp)
    (showa (prec PointOp) a . showPoint . showIdent i)