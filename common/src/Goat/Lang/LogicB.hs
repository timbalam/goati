{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
module Goat.Lang.LogicB
  where

import Goat.Comp
import Goat.Lang.Symbol
import Goat.Util ((<&>))
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
    
showLogicB :: Applicative m => LogicB a -> (a -> m ShowS) -> m ShowS
showLogicB (a :#|| b) s = liftA2 (showPad "||") (s a) (s b)
showLogicB (a :#&& b) s = liftA2 (showPad "&&") (s a) (s b)

fromLogicB
 :: (Applicative m, LogicB_ r) => LogicB a -> (a -> m r) -> m r
fromLogicB (a :#|| b) k = liftA2 (#||) (k a) (k b)
fromLogicB (a :#&& b) k = liftA2 (#&&) (k a) (k b)

instance Member LogicB LogicB where uprism = id

instance Member LogicB r => LogicB_ (Comp r a) where
  a #|| b = join (send (a :#|| b))
  a #&& b = join (send (a :#&& b))
