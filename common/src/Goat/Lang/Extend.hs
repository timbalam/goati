{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.Extend
  where

import Goat.Comp
import Control.Applicative (liftA2)
import Control.Monad (join)
import Text.Parsec.Text (Parser)

infixl 9 #, :#

-- | Parse a value extension
class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r

parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

data Extend ext a = a :# ext a
  deriving (Eq, Show)

showExtend
 :: Applicative m
 => (forall x . ext x -> (x -> m ShowS) -> m ShowS)
 -> Extend ext a -> (a -> m ShowS) -> m (ShowS)
showExtend sx (a :# x) sa = liftA2 (.) (sa a) (sx x sa)

fromExtend
 :: (Applicative m, Extend_ r)
 => (forall x . ext x -> (x -> m r) -> m (Ext r))
 -> Extend ext a -> (a -> m r) -> m r
fromExtend kx (a :# x) ka = liftA2 (#) (ka a) (kx x ka)

instance Member (Extend e) (Extend e) where uprism = id
instance MemberU Extend (Extend e) where
  type UIndex Extend (Extend e) = e  

instance MemberU Extend r => Extend_ (Comp r a) where
  type Ext (Comp r a) = UIndex Extend r (Comp r a)
  a # x = join (send (a :# x))
