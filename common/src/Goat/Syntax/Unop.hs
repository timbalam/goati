--{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Syntax.Unop
  where

import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))

data Unop a =
    NoUnop a
  | NegU (Unop a)
  | NotU (Unop a)
  deriving (Eq, Show)

class Unop_ r where
  neg_ :: r -> r
  not_ :: r -> r

instance Unop_ (Unop a) where
  neg_ = NegU
  not_ = NotU

showUnop
 :: (a -> ShowS) -> Unop a -> ShowS
showUnop sa =
  showU (showExtend sa (showParen True . showUnop sa))
  where
    showU sa (NegU a) = showSymbol "-" . sa a
    showU sa (NotU a) = showSymbol "!" . sa a
    showU sa a        = sa a
    
    showExtend se sa (NoUnop a) = se a
    showExtend se sa a          = sa a

parseUnop :: Unop_ r => Parser (r -> r)
parseUnop = 
  parseNeg <|> parseNot <|> return id
  where
    parseNeg = parseSymbol "-" >> return neg_
    parseNot = parseSymbol "!" >> return not_

fromUnop:: Unop_ r => (a -> r) -> Unop a -> r
fromUnop ka (NoUnop a) = ka a
fromUnop ka (NegU a) = neg_ (fromUnop ka a)
fromUnop ka (NotU a) = not_ (fromUnop ka a)
