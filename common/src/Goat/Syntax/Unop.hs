{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Syntax.Unop
  where
  
import Goat.Syntax.Symbol
import Control.Monad.Free.Church
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
  
  
data UnOp a =
    Neg a
  | Not a
  deriving (Eq, Show, Functor)
  
showUnOp :: (a -> ShowS) -> UnOp a -> ShowS
showUnOp showa (Neg a) = showSymbol Sub . showa a
showUnOp showa (Not a) = showSymbol Bang . showa a

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
  neg_ a = OpU (Neg (unF a))
  not_ a = OpU (Not (unF a))
  
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
    parseNeg = parseSymbol Sub >> return neg_
    parseNot = parseSymbol Bang >> return not_

fromUn :: Un_ r => Un r -> r
fromUn = fromOpU fromUnOp fromF where
  fromF (F f) = f id (fromOpU fromUnOp id)
  
  fromUnOp f (Not a) = not_ (f a)
  fromUnOp f (Neg a) = neg_ (f a)