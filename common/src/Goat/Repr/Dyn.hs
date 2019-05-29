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


checkMulti
 :: (Text -> e)
 -> (a -> ([e], b))
 -> Components NonEmpty Identity a 
 -> ([e], Components (Either e) (Either e) b)
checkMulti throwe k (Components (Extend kma (Identity a))) =
  Components <$>
    (Extend <$>
      Map.traverseWithKey (checkDuplicates k . throwe) kma <*>
      (Right <$> k a))
  where
    checkDuplicates 
     :: (a -> ([e], b)) -> e -> NonEmpty a -> ([e], Either e b)
    checkDuplicates f _e (a:|[]) = Right <$> f a
    checkDuplicates f e as = traverse_ f as >> ([e], Left e)

throwDyn :: e -> Dyn e a
throwDyn e = Components (Extend mempty (Left e))  

-- | Dynamic errors

type Dyn e = Components (Either e) (Either e)

mapError
 :: (e -> e')
 -> Components (Either e) (Either e) a
 -> Components (Either e') (Either e') a
mapError f (Components x) =
  Components (bimap (first f) (first f) x)
  
displayDyn :: (e -> String) -> (a -> String) -> Dyn e a -> String
displayDyn showe showa (Components (Extend kv ev)) =
  case (Map.keys kv, ev) of
    ([], Right a) -> showa a
    ([], Left e)  -> showe e
    (ks, ev)      -> "components: "
      ++ show (map Text.unpack ks)
      ++ ", "
      ++ either showe showa ev
