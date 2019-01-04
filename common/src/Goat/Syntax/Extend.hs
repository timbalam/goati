{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
module Goat.Syntax.Extend
  where


import Control.Monad.Free
import Text.Parsec.Text (Parser)



-- | Parse a value extension
data Extend x a = a :# x deriving (Eq, Show)

class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r
  
instance MonadFree (Extend x) m => Extend_ (Extend x (m a)) where
  type Ext (Extend x (m a)) = x
  a # x = wrap a :# x

  
parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

showExtend :: (x -> ShowS) -> (a -> ShowS) -> Extend x a -> ShowS
showExtend showx showa (a :# x) = showa a . showChar ' ' . showx x

fromExtend :: Extend_ r => Extend (Ext r) r -> r
fromExtend (a :# x) = a # x