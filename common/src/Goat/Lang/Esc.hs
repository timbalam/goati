{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.Esc
  where

import Goat.Comp
import Goat.Lang.Symbol
import Goat.Util ((<&>))
import Text.Parsec.Text (Parser)
import Control.Monad (join)
  
-- | Lift an expression to a higher scope (Deprecated syntax)
class Esc_ r where
  type Lower r
  esc_ :: Lower r -> r
  
parseEsc :: Esc_ r => Parser (Lower r -> r)
parseEsc = do
  parseSymbol "~"
  return esc_

data Esc l a = Esc (l a) deriving (Eq, Show)
  
showEsc
 :: Functor m => Esc l a -> (l a -> m ShowS) -> m ShowS
showEsc (Esc l) sl = sl l <&> \ a -> showSymbol "~" . a

fromEsc
 :: (Functor m, Esc_ r)
 => Esc lower a -> (lower a -> m (Lower r)) -> m r
fromEsc (Esc l) kl = esc_ <$> kl l

instance Member (Esc l) (Esc l) where uprism = id

instance MemberU Esc (Esc l) where
  type UIndex Esc (Esc l) = l
  
instance MemberU Esc r => Esc_ (Comp r a) where
  type Lower (Comp r a) = UIndex Esc r (Comp r a)
  esc_ l = join (send (Esc l))
