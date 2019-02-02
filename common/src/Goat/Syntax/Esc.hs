{-# LANGUAGE TypeFamilies #-}
module Goat.Syntax.Esc
  where

import Goat.Syntax.Symbol (showSymbol, parseSymbol)
import Text.Parsec.Text (Parser)
  
-- | Lift an expression to a higher scope
data Esc lwr a =
    NoEsc a
  | Esc lwr
  deriving (Eq, Show)

class Esc_ r where
  type Lower r
  esc_ :: Lower r -> r

instance Esc_ (Esc lwr a) where
  type Lower (Esc lwr a) = lwr
  esc_ = Esc
  
parseEsc :: Esc_ r => Parser (Lower r -> r)
parseEsc = do
  parseSymbol "~"
  return esc_
  
showEsc :: (lwr -> ShowS) -> (a -> ShowS) -> Esc lwr a -> ShowS
showEsc sl sa (NoEsc a) = sa a
showEsc sl sa (Esc l) = showSymbol "~" . sl l

fromEsc :: Esc_ r => (lwr -> Lower r) -> (a -> r) -> Esc lwr a -> r
fromEsc kl ka (NoEsc a) = ka a
fromEsc kl ka (Esc l) = esc_ (kl l)
