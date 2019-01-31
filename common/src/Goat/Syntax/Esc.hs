{-# LANGUAGE TypeFamilies #-}
module Goat.Syntax.Esc
  where

import Goat.Syntax.Symbol (showSymbol, parseSymbol)
import Text.Parsec.Text (Parser)
  
-- | Lift an expression to a higher scope
data Esc a = Esc a deriving (Eq, Show)

class Esc_ r where
  type Lower r
  esc_ :: Lower r -> r

instance Esc_ (Esc a) where
  type Lower (Esc a) = a
  esc_ = Esc
  
parseEsc :: Esc_ r => Parser (Lower r -> r)
parseEsc = do
  parseSymbol "~"
  return esc_
  
showEsc :: (a -> ShowS) -> Esc a -> ShowS
showEsc sa (Esc a) = showSymbol "~" . sa a

fromEsc :: Esc_ r => (a -> Lower r) -> Esc a -> r
fromEsc ka (Esc a) = esc_ (ka a)
