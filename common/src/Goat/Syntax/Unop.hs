{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Syntax.Unop
  where

import Goat.Syntax.Symbol
import Goat.Syntax.Infix
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))


data Unop a b =
    NegU a
  | NotU a
  deriving (Eq, Show, Functor)

showUnop :: (a -> ShowS) -> (b -> ShowS) -> Unop a b -> ShowS
showUnop sa _ (NegU a) = showSymbol Neg . sa a
showUnop sa sb (NotU a) = showSymbol Not . sa a

type Un f = Sum Identity (Op f (Assoc Unop f))

class Un_ r where
  neg_ :: r -> r
  not_ :: r -> r

instance Functor f => Un_ (Un f a) where
  neg_ a = prefixOp NegU a
  not_ a = prefixOp NotU a

showUn
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> Un f a -> ShowS
showUn sf =
  fromSum (. runIdentity) (showOp sf (showAssoc showUnop sf))

parseUn :: Un_ r => Parser (r -> r)
parseUn = 
  parseNeg <|> parseNot <|> return id
  where
    parseNeg = parseSymbol Neg >> return neg_
    parseNot = parseSymbol Not >> return not_

fromUn
 :: Un_ r
 => (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> Un f a -> r
fromUn kf =
  fromSum (. runIdentity) (fromOp kf (fromAssoc fromUnop kf))
  where
    fromUnop f _ (NegU a) = neg_ (f a)
    fromUnop f _ (NotU a) = not_ (f a)
