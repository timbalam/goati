{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeOperators #-}
module Goat.Lang.Unop
  where

import Goat.Comp
import Goat.Lang.Symbol
import Control.Monad (join)
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))


class Unop_ r where
  neg_ :: r -> r
  not_ :: r -> r

parseUnop :: Unop_ r => Parser (r -> r)
parseUnop = 
  parseNeg <|> parseNot <|> return id
  where
    parseNeg = parseSymbol "-" >> return neg_
    parseNot = parseSymbol "!" >> return not_

data Unop a =
    NegU a
  | NotU a
  deriving (Eq, Show)

instance Member Unop r => Unop_ (Comp r a) where
  neg_ a = join (send (NegU a))
  not_ a = join (send (NotU a))

showUnop
 :: Comp (Unop <: t) ShowS -> Comp t ShowS
showUnop = showUn (showNested showUnop)
  where
    showNested, showUn
     :: (Comp (Unop <: t) ShowS -> Comp t ShowS)
     -> Comp (Unop <: t) ShowS -> Comp t ShowS
    showNested sa (Done s)         = Done s
    showNested sa (Req (Tail t) k) = Req t (showNested sa . k)
    showNested sa m                = do
      a <- sa m
      return (showParen True a)
    
    showUn sa (Req (Head (NegU a)) k) =
      fmap (showUnop' . NegU) (sa (k a))
    showUn sa (Req (Head (NotU a)) k) =
      fmap (showUnop' . NotU) (sa (k a))
    showUn sa m                       = sa m
    
    showUnop' :: Unop ShowS -> ShowS
    showUnop' (NegU a) = showSymbol "-" . a
    showUnop' (NotU a) = showSymbol "!" . a

fromUnop:: Unop_ r => Comp (Unop <: t) r -> Comp t r
fromUnop = handle fromUnop' where
  fromUnop' (NegU a) k = fmap neg_ (k a)
  fromUnop' (NotU a) k = fmap not_ (k a)
