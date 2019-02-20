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
  
instance MemberU Esc r => Esc_ (Comp r a) where
  type Lower (Comp r a) = Dep Esc r
  esc_ l = send (Esc l)
  
showEsc
 :: (lwr -> ShowS) -> Comp (Esc lwr <: t) ShowS -> Comp t ShowS
showEsc sl = handle (\ (Esc l) _ ->
  return (showSymbol "~" . sl l))

fromEsc
 :: Esc_ r => (lwr -> Lower r) -> Comp (Esc lwr <: t) r -> Comp t r
fromEsc kl = handle (\ (Esc l) _ -> return (esc_ (kl l)))
