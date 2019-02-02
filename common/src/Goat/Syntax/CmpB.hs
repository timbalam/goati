module Goat.Syntax.CmpB
  where

import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Data.String (fromString)

-- Comparison operations
data CmpB a =
    NoCmpB a
  | CmpB a :#== CmpB a
  | CmpB a :#!= CmpB a
  | CmpB a :#<  CmpB a
  | CmpB a :#<= CmpB a
  | CmpB a :#>  CmpB a
  | CmpB a :#>= CmpB a
  deriving (Eq, Show)
  
class CmpB_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r

instance CmpB_ (CmpB a) where
  (#==) = (:#==)
  (#!=) = (:#!=)
  (#>)  = (:#>)
  (#>=) = (:#>=)
  (#<)  = (:#<)
  (#<=) = (:#<=)

showCmpB
 :: (a -> ShowS) -> CmpB a -> ShowS
showCmpB sa =
  showCmp (showArith sa (showParen True . showCmpB sa))
  where 
    showCmp sa (a :#== b) = sa a . showPad "==" . sa b
    showCmp sa (a :#!= b) = sa a . showPad "!=" . sa b
    showCmp sa (a :#>  b) = sa a . showPad ">"  . sa b
    showCmp sa (a :#>= b) = sa a . showPad ">=" . sa b
    showCmp sa (a :#<  b) = sa a . showPad "<"  . sa b
    showCmp sa (a :#<= b) = sa a . showPad "<=" . sa b
    showCmp sa a          = sa a
    
    showArith sr sa (NoCmpB a) = sr a
    showArith sr sa a         = sa a
    
showPad s =
  showChar ' ' . showSymbol s . showChar ' '


parseCmpB :: CmpB_ r => Parser r -> Parser r
parseCmpB p =
  do
    a <- p
    (do
       s <- cmpOp
       b <- p
       return (s a b))
      <|> return a
  where
    cmpOp = 
      (parseSymbol ">" >> return (#>))
        <|> (parseSymbol "<" >> return (#<))
        <|> (parseSymbol "==" >> return (#==))
        <|> (parseSymbol "!=" >> return (#!=))
        <|> (parseSymbol ">=" >> return (#>=))
        <|> (parseSymbol "<=" >> return (#<=))
    
fromCmpB
 :: CmpB_ r => (a -> r) -> CmpB a -> r
fromCmpB ka (NoCmpB a)  = ka a
fromCmpB ka (a :#== b) = fromCmpB ka a #== fromCmpB ka b
fromCmpB ka (a :#!= b) = fromCmpB ka a #!= fromCmpB ka b
fromCmpB ka (a :#>  b) = fromCmpB ka a #>  fromCmpB ka b
fromCmpB ka (a :#>= b) = fromCmpB ka a #>= fromCmpB ka b
fromCmpB ka (a :#<  b) = fromCmpB ka a #<  fromCmpB ka b
fromCmpB ka (a :#<= b) = fromCmpB ka a #<= fromCmpB ka b