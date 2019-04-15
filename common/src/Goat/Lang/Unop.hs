{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Goat.Lang.Unop
  where

import Goat.Comp
import Goat.Lang.Symbol
import Goat.Util ((<&>))
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

showUnop :: Functor m => Unop a -> (a -> m ShowS) -> m ShowS
showUnop (NegU a) k = k a <&> \ a -> showSymbol "-" . a
showUnop (NotU a) k = k a <&> \ a -> showSymbol "!" . a

fromUnop :: (Functor m, Unop_ r) => Unop a -> (a -> m r) -> m r
fromUnop (NegU a) k = neg_ <$> k a
fromUnop (NotU a) k = not_ <$> k a

instance Member Unop Unop where uprism = id  

instance Member Unop r => Unop_ (Comp r a) where
  neg_ a = join (send (NegU a))
  not_ a = join (send (NotU a))
