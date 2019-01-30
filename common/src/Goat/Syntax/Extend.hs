{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, DeriveFunctor #-}
module Goat.Syntax.Extend
  where

import Text.Parsec.Text (Parser)

infixl 9 #, :#

-- | Parse a value extension
data Extend x a =
    Path a
  | Extend x a :# x
  deriving (Eq, Show, Functor)

class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r
  
instance Extend_ (Extend x a) where
  type Ext (Extend x a) = x
  (#) = (:#)

  
parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

showExtend :: (x -> ShowS) -> (a -> ShowS) -> Extend x a -> ShowS
showExtend sx sa (Path a) = sa a
showExtend sx sa (a :# x) = showExtend sx sa a . sx x

fromExtend
 :: Extend_ r => (x -> Ext r) -> (a -> r) -> Extend x a -> r
fromExtend kx ka (Path a) = ka a
fromExtend kx ka (a :# x) = fromExtend kx ka a # kx x