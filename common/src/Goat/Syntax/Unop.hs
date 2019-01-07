{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Syntax.Unop
  where

import Goat.Syntax.Symbol
import Goat.Syntax.Fixity
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

type ArithU = Prefix NegOp

class ArithU_ r where
  neg_ :: r -> r

unTerm
 :: MonadFree (Prefix f) m => Prefix f (m a) -> m a
unTerm (TermP a) = a
unTerm a         = wrap a

instance MonadFree ArithU m => ArithU_ (ArithU (m a)) where
  neg_ a = Prefix (NegU (unTerm a))

showArithU :: (a -> ShowS) -> ArithU (F ArithU a) -> ShowS
showArithU showa = fromPrefix showNegOp (\ (F f) -> 
  f showa (fromPrefix showNegOp id))

parseArithU :: ArithU_ r => Parser (r -> r)
parseArithU = 
  parseNeg <|> return id
  where
    parseNeg = parseSymbol Neg >> return neg_

fromArithU :: ArithU_ r => ArithU (F ArithU r) -> r
fromArithU = fromPrefix fromNegOp (iter (fromPrefix fromNegOp id)) where
  fromNegOp f (NegU a) = neg_ (f a)


type LogicU = Prefix NotOp

class LogicU_ r where
  not_ :: r -> r

instance MonadFree LogicU m => LogicU_ (LogicU (m a)) where
  not_ a = Prefix (NotU (unTerm a))

showLogicU :: (a -> ShowS) -> LogicU (F LogicU a) -> ShowS
showLogicU showa = fromPrefix showNotOp (\ (F f) ->
  f showa (fromPrefix showNotOp id))

parseLogicU :: LogicU_ r => Parser (r -> r)
parseLogicU = 
  parseNot <|> return id
  where
    parseNot = parseSymbol Not >> return not_

fromLogicU :: LogicU_ r => LogicU (F LogicU r) -> r
fromLogicU = fromPrefix fromNotOp (iter (fromPrefix fromNotOp id)) where
  fromNotOp f (NotU a) = not_ (f a)
