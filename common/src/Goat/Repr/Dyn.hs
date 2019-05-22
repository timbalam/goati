{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

-- | This module implements some data types and definitions for represent Goat values that track errors dynamically.
-- It defines a data type 'Dyn': a wrapper for injecting dynamic errors inside a storage type.

module Goat.Repr.DynMap where

import Goat.Repr.Pattern
  (Extend(..), Inside(..), Multi, Map, Text, Ident)
import Goat.Util ((<&>))
import Data.Bifunctor (first)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map


checkExtension
 :: (Text -> e) -> Components a -> ([e], Dyn e a)
checkExtension throw (Components (Extend kv v)) =
  Map.traverseWithKey
    (checkDuplicates . throw)
    kv <&> \ kv' -> Dyn (Extend kv' v)
  where
    checkDuplicates 
     :: e -> NonEmpty a -> ([e], Either e a)
    checkDuplicates _e (a:|[]) = ([], Right a)
    checkDuplicates e _ = ([e], Left e)

-- | Dynamic errors

data Dyn e a = Dyn (Extend (Map Text) (Either e a) a)
  deriving (Functor, Foldable, Traversable)

mapError
 :: Functor f => (e -> e') -> Dyn e f a -> Dyn e' f a
mapError f (Dyn fe) = Dyn (first f <$> fe)

-- | Errors from binding definitions

data DefnError =
    OlappedMatch Ident
    -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet Ident
    -- ^ Error if a group assigns to non-disjoint paths
  | DuplicateImport Ident
    -- ^ Error if an import name is duplicated
  deriving (Eq, Show)
  
  
displayDefnError :: DefnError -> String
displayDefnError (OlappedMatch i) =
  "error: Multiple component matches for name: " ++ show i
displayDefnError (OlappedSet i) =
  "error: Multiple assignments for name: " ++ show i
displayDefnError (DuplicateImport i) =
  "error: Multiple imports with name: " ++ show i
