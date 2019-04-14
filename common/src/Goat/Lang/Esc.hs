{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances #-}
module Goat.Lang.Esc
  where

import Goat.Comp
import Goat.Lang.Symbol
import Text.Parsec.Text (Parser)
  
-- | Lift an expression to a higher scope (Deprecated syntax)
class Esc_ r where
  type Lower r
  esc_ :: Lower r -> r
  
parseEsc :: Esc_ r => Parser (Lower r -> r)
parseEsc = do
  parseSymbol "~"
  return esc_

data Esc lwr a = Esc lwr deriving (Eq, Show)
  
showEsc :: (lwr -> ShowS) -> Esc lwr -> ShowS
showEsc sl (Esc l) = showSymbol "~" . sl l

fromEsc :: Esc_ r => (lwr -> Lower r) -> Esc lwr -> r
fromEsc kl (Esc l) = esc_ (kl l)

instance Member (Esc l) (Esc l) where
  uprism = id

instance MemberU Esc (Esc l) where
  type UIndex (Esc l) = l
  
instance MemberU Esc r => Esc_ (Comp r a) where
  type Lower (Comp r a) = UIndex Esc r
  esc_ l = send (Esc l)
