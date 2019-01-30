module Goat.Syntax.LogicB
  where

import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Data.String (fromString)

-- Logical operations
data LogicB a =
    Cmp a
  | LogicB a :#&& LogicB a
  | LogicB a :#|| LogicB a
  deriving (Eq, Show)

class LogicB_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r
  
instance LogicB_ (LogicB a) where
  (#||) = (:#||)
  (#&&) = (:#&&)
  
showLogicB
 :: (a -> ShowS) -> LogicB a -> ShowS
showLogicB sa =
  showOr (showAnd (showCmp sa (showParen True . showLogicB sa)))
  where
    showOr sa (a :#|| b) = showOr sa a . showPad "||" . sa b
    showOr sa a          = sa a
  
    showAnd sa (a :#&& b) = showAnd sa a . showPad "&&" . sa b
    showAnd sa a          = sa a
    
    showCmp sc sa (Cmp a) = sc a
    showCmp sc sa a       = sa a
    
showPad s =
  showChar ' ' . showSymbol s . showChar ' '

parseLogicB :: LogicB_ r => Parser r -> Parser r
parseLogicB p = parseOrB (parseAndB p)
  where
    parseOrB p = Parsec.chainr1 p orOp where
      orOp = parseSymbol "||" >> return (#||)
    
    parseAndB p = Parsec.chainr1 p andOp where
      andOp = parseSymbol "&&" >> return (#&&)
      
fromLogicB
 :: LogicB_ r => (a -> r) -> LogicB a -> r
fromLogicB ka (Cmp a)    = ka a
fromLogicB ka (a :#|| b) = fromLogicB ka a #|| fromLogicB ka b
fromLogicB ka (a :#&& b) = fromLogicB ka a #&& fromLogicB ka b