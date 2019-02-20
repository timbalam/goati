{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, RankNTypes #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.LogicB
  where

import Goat.Comp
import Goat.Lang.ArithB (showPad)
import Goat.Lang.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Control.Applicative (liftA2)
import Control.Monad (join)
import Data.String (fromString)

-- Logical operations
class LogicB_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r

parseLogicB :: LogicB_ r => Parser r -> Parser r
parseLogicB p = parseOrB (parseAndB p)
  where
    parseOrB p = Parsec.chainr1 p orOp where
      orOp = parseSymbol "||" >> return (#||)
    
    parseAndB p = Parsec.chainr1 p andOp where
      andOp = parseSymbol "&&" >> return (#&&)

data LogicB a =
    a :#&& a
  | a :#|| a
  deriving (Eq, Show)

instance Member LogicB r => LogicB_ (Comp r a) where
  a #|| b = join (send (a :#|| b))
  a #&& b = join (send (a :#&& b))
  
showLogicB
 :: Comp (LogicB <: t) ShowS -> Comp t ShowS
showLogicB = showAnd (showOr (showNested showLogicB))
  where
    showOr, showAnd, showNested
     :: (Comp (LogicB <: t) ShowS -> Comp t ShowS)
     -> Comp (LogicB <: t) ShowS -> Comp t ShowS
    showNested sa (Done s) = Done s
    showNested sa (Req (Tail t) k) = Req t (showNested sa . k)
    showNested sa m = do
      a <- sa m
      return (showParen True a)
    
    showOr sa (Req (Head (a :#|| b)) k) = do
      a <- showOr sa (k a)
      b <- sa (k b)
      return (showLogicB' (a :#|| b))
    showOr sa m                         = sa m
  
    showAnd sa (Req (Head (a :#&& b)) k) = do
      a <- showAnd sa (k a)
      b <- sa (k b)
      return (showLogicB' (a :#&& b))
    showAnd sa m                         = sa m
    
    showLogicB' :: LogicB ShowS -> ShowS
    showLogicB' (a :#|| b) = a . showPad "||" . b
    showLogicB' (a :#&& b) = a . showPad "&&" . b
    

fromLogicB
 :: LogicB_ r => Comp (LogicB <: t) r -> Comp t r
fromLogicB = handle fromLogicB'
  where
    fromLogicB' (a :#|| b) k = liftA2 (#||) (k a) (k b)
    fromLogicB' (a :#&& b) k = liftA2 (#&&) (k a) (k b)
