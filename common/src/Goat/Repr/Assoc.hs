{-# LANGUAGE DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Goat.Repr.Assoc
  where

import Goat.Lang.Ident (Ident)
import Data.Align
import Data.Functor.Plus (Alt(..), Plus(..))
import Data.Map (Map)
import qualified Data.Map as Map


newtype Assoc a = Assoc (Map Ident a)
  deriving (Align, Functor, Foldable, Traversable)
{-
instance Alt Assoc where Assoc a <!> Assoc b = Assoc (a <!> b)
instance Plus Assoc where zero = Assoc zero
-}

singleton :: Ident -> a -> Assoc a
singleton k a = Assoc (Map.singleton k a)

insert :: Ident -> a -> Assoc a -> Assoc a
insert k a (Assoc kv) = Assoc (Map.insert k a kv)

--empty :: Assoc a
--empty = Assoc Map.empty

mapWithKey :: (Ident -> a -> b) -> Assoc a -> Assoc b
mapWithKey f (Assoc kv) = Assoc (Map.mapWithKey f kv)

foldMapWithKey
 :: Monoid m => (Ident -> a -> m) -> Assoc a -> m
foldMapWithKey f (Assoc kv) = Map.foldMapWithKey f kv

traverseWithKey
 :: Applicative f => (Ident -> a -> f b) -> Assoc a -> f (Assoc b)
traverseWithKey f (Assoc kv) =
  Assoc <$> Map.traverseWithKey f kv

mapMaybe :: (a -> Maybe b) -> Assoc a -> Assoc b
mapMaybe f (Assoc kv) = Assoc (Map.mapMaybe f kv)

mapEither
 :: (a -> Either b c) -> Assoc a -> (Assoc b, Assoc c)
mapEither f (Assoc ka) = (Assoc kb, Assoc kc)
  where
    (kb, kc) = Map.mapEither f ka

lookup :: Ident -> Assoc a -> Maybe a
lookup k (Assoc kv) = Map.lookup k kv
