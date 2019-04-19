{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, RankNTypes, ConstraintKinds #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.Extend
  where

import Goat.Comp
import Control.Applicative (liftA2)
import Control.Monad (join)
import Data.Functor.Identity (Identity(..))
import Data.Void (Void)
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))

infixl 9 #, :#

-- | Parse a value extension
class Extend_ r where
  type Extension r
  type Ext r
  (#) :: Ext r -> Extension r -> r

parseExtend :: Extend_ r => Parser (Ext r -> Extension r -> r)
parseExtend = pure (#)

data Extend ext extn a = ext :# extn
  deriving (Eq, Show)

showExtend
 :: Applicative m
 => (ext -> m ShowS)
 -> (extn -> m ShowS)
 -> Extend ext extn a -> m ShowS
showExtend se sx (e :# x) = liftA2 (.) (se e) (sx x)

fromExtend
 :: (Applicative m, Extend_ r)
 => (ext -> m (Ext r))
 -> (extn -> m (Extension r))
 -> Extend ext extn a -> m r
fromExtend ke kx (e :# x) = liftA2 (#) (ke e) (kx x)

instance Extend_ (Extend ext extn a) where
  type Extension (Extend ext extn a) = extn
  type Ext (Extend ext extn a) = ext
  (#) = (:#)

instance MemberU2 Extend r => Extend_ (Comp r a) where
  type Extension (Comp r a) = U1Index Extend r
  type Ext (Comp r a) = U2Index Extend r
  a # x = send (a :# x)


type ExtendChain_ r x = (Extend_ r, Ext r ~ r, Extension r ~ x)

parseExtendLink
 :: (Extend_ r, ExtendChain_ (Ext r) (Extension r))
 => Parser (Extension r) -> Parser (Ext r -> r)
parseExtendLink px = do
  ext <- parseExtend
  x <- px
  (do 
    g <- parseExtendLink px
    return (g . cloneExtend . (`ext` x))) <|>
    return (cloneExtend . (`ext` x))
  
cloneExtend
 :: Extend_ r => Extend (Ext r) (Extension r) Void -> r
cloneExtend = runIdentity . fromExtend pure pure
