{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

-- | This module implements some data types and definitions for represent Goat values that track errors dynamically.
-- It defines a data type 'Dyn': a wrapper for injecting dynamic errors inside a storage type.

module Goat.Repr.Dyn where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>))
import Data.Bifunctor (bimap, first)
import Data.Bitraversable (bitraverse)
import Data.Foldable (traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import qualified Data.Text as Text


type DynCpts e = Inside (Either e) (Map Text)

checkComponents
 :: (Text -> e)
 -> (a -> ([e], b))
 -> AmbigCpts a 
 -> ([e], DynCpts e b)
checkComponents throwe k (Inside kma) 
  = Inside
 <$> Map.traverseWithKey
      (checkDuplicates k . throwe)
      kma
  where
    checkDuplicates 
     :: (a -> ([e], b))
     -> e
     -> NonEmpty a
     -> ([e], Either e b)
    checkDuplicates f _e (a:|[])
      = Right <$> f a
    
    checkDuplicates f e as
      = traverse_ f as >> ([e], Left e)
{-
throwDyn :: e -> DynCpts e a
throwDyn e = Components (Extend mempty (Left e))  
-}
-- | Dynamic errors

mapError
 :: Functor f
 => (e -> e')
 -> Inside (Either e) f a
 -> Inside (Either e') f a
mapError f (Inside fea)
  = Inside (first f <$> fea)

displayDynCpts
 :: DynCpts e a -> String
displayDynCpts (Inside kv)
  = "components: "
 ++ show (map Text.unpack (Map.keys kv))
