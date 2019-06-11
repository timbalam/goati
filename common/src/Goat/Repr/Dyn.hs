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
import Prelude.Extras (Eq1(..), Show1(..))


data DynCpts e a
  = DynCpts (Map Text (Either e a)) (Maybe e)
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Eq e => Eq1 (DynCpts e)
instance Show e => Show1 (DynCpts e)

checkComponents
 :: Monoid m
 => (m -> e)
 -> (a -> ([e], b))
 -> Cpts ((,) m) a 
 -> ([e], DynCpts e b)
checkComponents throwe f (Inside kps)
  = traverse
      (\ (Ambig ps)
       -> checkDuplicates f
            (throwe (foldMap fst ps))
            (snd <$> ps))
      kps
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

throwDyn :: e -> DynCpts e a
throwDyn e = DynCpts Map.empty (Just e)  

-- | Dynamic errors

mapError
 :: (e -> e')
 -> DynCpts e a -> DynCpts e' a
mapError f (DynCpts fea me)
  = DynCpts (first f <$> fea) (f <$> me)

displayDynCpts
 :: (e -> String) -> DynCpts e a -> String
displayDynCpts showe (DynCpts kv me)
  = "components: "
 ++ show (map Text.unpack (Map.keys kv))
 ++ maybe "" (showString "," . showe) me
