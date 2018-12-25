{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Syntax.Unop
  where
  
import Goat.Syntax.Symbol
import Control.Monad.Free.Church
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
  
  
data UnOp a =
    NegU a
  | NotU a
  deriving (Eq, Show, Functor)
  
showUnOp :: (a -> ShowS) -> UnOp a -> ShowS
showUnOp showa (NegU a) = showSymbol Neg . showa a
showUnOp showa (NotU a) = showSymbol Not . showa a

data OpU f a =
    LiftU a
  | OpU (f a)
  deriving (Eq, Show, Functor)
  
fromOpU
  :: (forall x . (x -> r) -> f x -> r)
  -> (a -> r) -> OpU f a -> r
fromOpU showf showa (LiftU a) = showa a
fromOpU showf showa (OpU f) = showf showa f
  
class Un_ r where
  neg_ :: r -> r
  not_ :: r -> r
  
type Un a = OpU UnOp (F (OpU UnOp) a)

unF :: MonadFree (OpU UnOp) m => OpU UnOp (m a) -> m a
unF (LiftU a) = a
unF a         = wrap a
  
instance Un_ (Un r) where
  neg_ a = OpU (NegU (unF a))
  not_ a = OpU (NotU (unF a))
  
showUn :: (a -> ShowS) -> Un a -> ShowS
showUn showa = fromOpU showUnOp (showF showa)
  where 
    showF showa (F f) = f showa (fromOpU showUnOp id)

parseUn :: Un_ r => Parser (r -> r)
parseUn = (do 
  f <- parseNeg <|> parseNot
  g <- parseUn
  return (f . g))
  <|> return id
  where
    parseNeg = parseSymbol Neg >> return neg_
    parseNot = parseSymbol Not >> return not_

fromUn :: Un_ r => Un r -> r
fromUn = fromOpU fromUnOp fromF where
  fromF (F f) = f id (fromOpU fromUnOp id)
  
  fromUnOp f (NegU a) = neg_ (f a)
  fromUnOp f (NotU a) = not_ (f a)