{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Syntax.Unop
  where
  
import Goat.Syntax.Symbol
import Control.Monad.Free.Church
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
  
  
data NegOp a = NegU a
  deriving (Eq, Show, Functor)
  
showNegOp :: (a -> ShowS) -> NegOp a -> ShowS
showNegOp showa (NegU a) = showSymbol Neg . showa a

data NotOp a = NotU a
  deriving (Eq, Show, Functor)
  
showNotOp :: (a -> ShowS) -> NotOp a -> ShowS
showNotOp showa (NotU a) = showSymbol Not . showa a

data UnopA f a =
    LiftU a
  | UnopA (f a)
  deriving (Eq, Show, Functor)
  
fromUnopA
  :: (forall x . (x -> r) -> f x -> r)
  -> (a -> r) -> UnopA f a -> r
fromUnopA showf showa (LiftU a) = showa a
fromUnopA showf showa (UnopA f) = showf showa f

type ArithUn a = UnopA NegOp (F (UnopA NegOp) a)

class ArithUn_ r where
  neg_ :: r -> r
  
unF
 :: MonadFree (UnopA f) m => UnopA f (m a) -> m a
unF (LiftU a) = a
unF a         = wrap a

instance ArithUn_ (ArithUn a) where
  neg_ a = UnopA (NegU (unF a))
  
showArithUn :: (a -> ShowS) -> ArithUn a -> ShowS
showArithUn showa = fromUnopA showNegOp (showF showa)
  where 
    showF showa (F f) = f showa (fromUnopA showNegOp id)

parseArithUn :: ArithUn_ r => Parser (r -> r)
parseArithUn = 
  parseNeg <|> return id
  where
    parseNeg = parseSymbol Neg >> return neg_

fromArithUn :: ArithUn_ r => ArithUn r -> r
fromArithUn = fromUnopA fromNegOp fromF where
  fromF (F f) = f id (fromUnopA fromNegOp id)
  fromNegOp f (NegU a) = neg_ (f a)
  
  
type LogicUn a = UnopA NotOp (F (UnopA NotOp) a)
  
class LogicUn_ r where
  not_ :: r -> r
  
instance LogicUn_ (LogicUn r) where
  not_ a = UnopA (NotU (unF a))
  
showLogicUn :: (a -> ShowS) -> LogicUn a -> ShowS
showLogicUn showa = fromUnopA showNotOp (showF showa)
  where 
    showF showa (F f) = f showa (fromUnopA showNotOp id)

parseLogicUn :: LogicUn_ r => Parser (r -> r)
parseLogicUn = 
  parseNot <|> return id
  where
    parseNot = parseSymbol Not >> return not_

fromLogicUn :: LogicUn_ r => LogicUn r -> r
fromLogicUn = fromUnopA fromNotOp fromF where
  fromF (F f) = f id (fromUnopA fromNotOp id)
  fromNotOp f (NotU a) = not_ (f a)