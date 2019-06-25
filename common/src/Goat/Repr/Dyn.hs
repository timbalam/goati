{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

-- | This module implements some data types and definitions for represent Goat values that track errors dynamically.
-- It defines a data type 'Dyn': a wrapper for injecting dynamic errors inside a storage type.

module Goat.Repr.Dyn where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>))
import Data.Bifunctor (bimap, first)
import Data.Bitraversable (bitraverse)
import Data.Discrimination
  (runGroup, Grouping(..), nubWith)
import Data.Foldable (traverse_)
import Data.Functor.Identity (runIdentity)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Text as Text
import Prelude.Extras (Eq1(..), Show1(..))


data DynCpts e a b
  = DynCpts (Map a (Either e b)) (Maybe e)
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq e, Eq a) => Eq1 (DynCpts e a)
instance (Show e, Show a) => Show1 (DynCpts e a)

checkComponents
 :: (Grouping k)
 => (m -> e)
 -> (a -> ([e], b))
 -> AnnCpts m k a 
 -> ([e], DynCpts e k b)
checkComponents throwe f (Components kv)
  = Map.traverseWithKey
      (\ k (m, as)
       -> checkDuplicates f (throwe m) as)
      kv
 <&> (`DynCpts` Nothing)
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

throwDyn :: e -> DynCpts e a b
throwDyn e = DynCpts Map.empty (Just e)  

-- | Dynamic errors

mapError
 :: (e -> e')
 -> DynCpts e a b -> DynCpts e' a b
mapError f (DynCpts kv me)
  = DynCpts (first f <$> kv) (f <$> me)

displayDynCpts
 :: (e -> String)
 -> (a -> String)
 -> DynCpts e a b -> String
displayDynCpts showe showk (DynCpts kv me)
  = "components: "
 ++ show (map showk (Map.keys kv))
 ++ maybe "" (showString "," . showe) me
