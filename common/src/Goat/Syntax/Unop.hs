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

type ArithU = UnopA NegOp

class ArithU_ r where
  neg_ :: r -> r

unF
 :: MonadFree (UnopA f) m => UnopA f (m a) -> m a
unF (LiftU a) = a
unF a         = wrap a

instance MonadFree ArithU m => ArithU_ (ArithU (m a)) where
  neg_ a = UnopA (NegU (unF a))

showArithU :: (a -> ShowS) -> ArithU (F ArithU a) -> ShowS
showArithU showa = fromUnopA showNegOp (\ (F f) -> 
  f showa (fromUnopA showNegOp id))

parseArithU :: ArithU_ r => Parser (r -> r)
parseArithU = 
  parseNeg <|> return id
  where
    parseNeg = parseSymbol Neg >> return neg_

fromArithU :: ArithU_ r => ArithU (F ArithU r) -> r
fromArithU = fromUnopA fromNegOp (iter (fromUnopA fromNegOp id)) where
  fromNegOp f (NegU a) = neg_ (f a)


type LogicU = UnopA NotOp

class LogicU_ r where
  not_ :: r -> r

instance MonadFree LogicU m => LogicU_ (LogicU (m a)) where
  not_ a = UnopA (NotU (unF a))

showLogicU :: (a -> ShowS) -> LogicU (F LogicU a) -> ShowS
showLogicU showa = fromUnopA showNotOp (\ (F f) ->
  f showa (fromUnopA showNotOp id))

parseLogicU :: LogicU_ r => Parser (r -> r)
parseLogicU = 
  parseNot <|> return id
  where
    parseNot = parseSymbol Not >> return not_

fromLogicU :: LogicU_ r => LogicU (F LogicU r) -> r
fromLogicU = fromUnopA fromNotOp (iter (fromUnopA fromNotOp id)) where
  fromNotOp f (NotU a) = not_ (f a)
