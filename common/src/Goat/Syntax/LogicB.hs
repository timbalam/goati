{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, RankNTypes #-}
module Goat.Syntax.LogicB
  where

import Goat.Co
import Goat.Syntax.ArithB (layer, showPad)
import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
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

instance LogicB_ (Flip Comp a (LogicB <: t)) where
  a #|| b = fsend (a :#|| b)
  a #&& b = fsend (a :#&& b)
  
showLogicB
 :: (Comp t ShowS -> ShowS)
 -> Comp (LogicB <: t) ShowS -> ShowS
showLogicB st = st . showOp showLogic
  where
    showOp
     :: ( forall x
           . LogicB x
          -> (x -> Comp (LogicB <: t) ShowS)
          -> Comp t ShowS
        )
     -> Comp (LogicB <: t) ShowS
     -> Comp t ShowS
    showOp = layer (showOp showLogic)
    
    showLogic
     :: LogicB a
     -> (a -> Comp (LogicB <: t) ShowS)
     -> Comp t ShowS
    showLogic =
      showAnd (showOr showNested)
      
    showNested h k= do
      a <- showLogic h k
      return (showParen True a)
    
    showOr, showAnd
      :: ( forall x
             . LogicB x
            -> (x -> Comp (LogicB <: t) ShowS)
            -> Comp t ShowS
         )
      -> LogicB a
      -> (a -> Comp (LogicB <: t) ShowS)
      -> Comp t ShowS
    showOr sa (a :#|| b) k = do
      a <- showOp (showOr sa) (k a)
      b <- showOp sa (k b)
      return (showLogicB' id (a :#|| b))
    showOr sa h          k = sa h k
  
    showAnd sa (a :#&& b) k = do
      a <- showOp (showAnd sa) (k a)
      b <- showOp sa (k b)
      return (showLogicB' id (a :#&& b))
    showAnd sa h          k = sa h k
    
    showLogicB' :: (a -> ShowS) -> LogicB a -> ShowS
    showLogicB' sa (a :#|| b) = sa a . showPad "||" . sa b
    showLogicB' sa (a :#&& b) = sa a . showPad "&&" . sa b
    

fromLogicB
 :: LogicB_ r
 => (Comp t r -> r)
 -> Comp (LogicB <: t) r -> r
fromLogicB kt =
  kt . handle (\ h k -> return (fromLogicB' (kt . k) h))
  where
    fromLogicB' ka (a :#|| b) = ka a #|| ka b
    fromLogicB' ka (a :#&& b) = ka a #&& ka b