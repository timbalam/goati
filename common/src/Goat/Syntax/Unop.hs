{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Goat.Syntax.Unop
  where
  
import Goat.Syntax.Symbol
import Control.Monad.Free
import Text.Parsec.Text (Parser)
  
  
data UnOp a =
    Neg a
  | Not a
  deriving (Eq, Show)
  
showUnOp :: (a -> ShowS) -> UnOp a -> ShowS
showUnOp f (Neg a) = showSymbol Sub (f a)
showUnOp f (Not a) = showSymbol Not (f a)

data OpU f a =
    LiftU a
  | OpU (f a)
  deriving (Eq, Show)
  
fromOpU
  :: (forall x . (x -> r) -> f x -> r)
  -> (a -> r) -> OpU f a -> r
fromOpU showf showa (LiftU a) = showa a
fromOpU showf showa (OpU f) = showf showa f
  
class Un_ r where
  neg_ :: r -> r
  not_ :: r -> r
  
type Un a = OpU UnOp (F (OpU UnOp) a)
  
instance Un_ (Un r) where
  neg_ m = OpU (Neg (f m))
  not_ m = OpU (Not (f m))
  
  f (LiftU a) = a
  f a         = LiftU (wrap a)
  
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
    parseNot = parseSymbol Not >> return not_

fromUn :: Un_ r => Un r -> r
fromUn = fromOpU fromUnOp fromF where
  fromF (F f) = f id fromUnOp
  
  fromUnOp (Not a) = not_ a
  fromUnOp (Neg a) = neg_ a