module Goat.Syntax.ArithB
  where

import Goat.Syntax.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)

infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-

-- Arithmetic operations
data ArithB a =
    Unop a
  | ArithB a :#+ ArithB a
  | ArithB a :#- ArithB a
  | ArithB a :#* ArithB a
  | ArithB a :#/ ArithB a
  | ArithB a :#^ ArithB a
  deriving (Eq, Show)

class ArithB_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
    
instance ArithB_ (ArithB a) where
  (#+) = (:#+)
  (#-) = (:#-)
  (#*) = (:#*)
  (#/) = (:#/)
  (#^) = (:#^)
  
showArithB
 :: (a -> ShowS) -> ArithB a -> ShowS
showArithB sa =
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
    
    showUn su sa (Unop a) = su a
    showUn su sa a        = sa a

showPad s = showChar ' ' . showSymbol s . showChar ' '


-- | Parse an expression observing operator precedence
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
       
fromArithB :: ArithB_ r => (a -> r) -> ArithB a -> r
fromArithB ka (Unop a) = ka a
fromArithB ka (f :#+ g) = fromArithB ka f #+ fromArithB ka g
fromArithB ka (f :#- g) = fromArithB ka f #- fromArithB ka g
fromArithB ka (f :#* g) = fromArithB ka f #* fromArithB ka g
fromArithB ka (f :#/ g) = fromArithB ka f #/ fromArithB ka g
fromArithB ka (f :#^ g) = fromArithB ka f #^ fromArithB ka g 
