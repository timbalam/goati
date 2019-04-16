{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RankNTypes #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.Extend
  where

import Goat.Comp
import Control.Applicative (liftA2)
import Control.Monad (join)
import Data.Functor.Identity (Identity(..))
import Data.Void (Void)
import Text.Parsec.Text (Parser)

infixl 9 #, :#

-- | Parse a value extension
class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r

parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

data Extend ext a = a :# ext
  deriving (Eq, Show)

showExtend
 :: Applicative m
 => (ext -> m ShowS)
 -> Extend ext a -> (a -> m ShowS) -> m (ShowS)
showExtend sx (a :# x) sa = liftA2 (.) (sa a) (sx x)

fromExtend
 :: (Applicative m, Extend_ r)
 => (ext -> m (Ext r))
 -> Extend ext a -> (a -> m r) -> m r
fromExtend kx (a :# x) ka = liftA2 (#) (ka a) (kx x)

instance Member (Extend e) (Extend e) where uprism = id
instance MemberU Extend (Extend e) where
  type UIndex Extend (Extend e) = e  

instance MemberU Extend r => Extend_ (Comp r a) where
  type Ext (Comp r a) = UIndex Extend r
  a # x = join (send (a :# x))

cloneExtend
 :: Extend_ r => Comp (Extend (Ext r)) a -> r -> r
cloneExtend m r =
  runIdentity
    (iter
      (fromExtend pure)
      (\ _ -> pure r)
      m)
