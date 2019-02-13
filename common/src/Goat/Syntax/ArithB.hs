module Goat.Syntax.ArithB
  where

import Goat.Co
import Goat.Syntax.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)

infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-

-- Arithmetic operations
class ArithB_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r

-- | Observe operator precedence
parseArithB :: ArithB_ r => Parser r -> Parser r
parseArithB p =
  parseAddB (parseMulB (parsePowB p))
  where
    parseAddB p = Parsec.chainl1 p addOp
    parseMulB p = Parsec.chainl1 p mulOp
    parsePowB p = Parsec.chainr1 p powOp
    
    addOp =
      (parseSymbol "+" >> return (#+))
        <|> (parseSymbol "-" >> return (#-))
    mulOp =
      (parseSymbol "*" >> return (#*))
        <|> (parseSymbol "/" >> return (#/))
    powOp = parseSymbol "^" >> return (#^)

data ArithB a =
    a :#+ a
  | a :#- a
  | a :#* a
  | a :#/ a
  | a :#^ a
  deriving (Eq, Show)
    
instance ArithB_ (Flip Comp a (ArithB <: t)) where
  a #+ b = send (a :#+ b)
  a #- b = send (a :#- b)
  a #* b = send (a :#* b)
  a #/ b = send (a :#/ b)
  a #^ b = send (a :#^ b)
  
showArithB
 :: (Comp t ShowS -> ShowS)
 -> Comp (ArithB <: t) ShowS -> ShowS
showArithB st =
  st . handle (\ op k ->
    showAdd'
      (showMul'
        (showPow'
  showAdd
    (showMul
      (showPow (showUn sa (showParen True . showArithB sa))))
  where
    showAdd sa (a :#+ b) = sa a . showPad "+" . showAdd sa b
    showAdd sa (a :#- b) = sa a . showPad "-" . showAdd sa b
    showAdd sa a         = sa a
    
    showMul sa (a :#* b) = sa a . showPad "*" . showMul sa b
    showMul sa (a :#/ b) = sa a . showPad "/" . showMul sa b
    showMul sa a         = sa a
    
    showPow sa (a :#^ b) = showPow sa a . showPad "^" . sa a
    showPow sa a         = sa a
    
    showUn su sa (NoArithB a) = su a
    showUn su sa a        = sa a

showPad s = showChar ' ' . showSymbol s . showChar ' '

       
fromArithB :: ArithB_ r => (a -> r) -> ArithB a -> r
fromArithB ka (NoArithB a) = ka a
fromArithB ka (f :#+ g) = fromArithB ka f #+ fromArithB ka g
fromArithB ka (f :#- g) = fromArithB ka f #- fromArithB ka g
fromArithB ka (f :#* g) = fromArithB ka f #* fromArithB ka g
fromArithB ka (f :#/ g) = fromArithB ka f #/ fromArithB ka g
fromArithB ka (f :#^ g) = fromArithB ka f #^ fromArithB ka g 
