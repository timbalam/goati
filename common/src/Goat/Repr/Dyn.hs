{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

-- | This module implements some data types and definitions for represent Goat values that track errors dynamically.
-- It defines a data type 'Dyn': a wrapper for injecting dynamic errors inside a storage type.

module Goat.Repr.Dyn where

import Goat.Repr.Pattern
  (Extend(..), Components(..), Ident, Identity(..), Text)
import Goat.Util ((<&>))
import Data.Bifunctor (bimap, first)
import Data.Bitraversable (bitraverse)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map


checkMulti
 :: (Text -> e)
 -> Components NonEmpty Identity a 
 -> ([e], Components (Either e) (Either e) a)
checkMulti throw (Components (Extend kma (Identity a))) =
  Components . (`Extend` Right a) <$>
  Map.traverseWithKey (checkDuplicates . throw) kma
  where
    checkDuplicates 
     :: e -> NonEmpty a -> ([e], Either e a)
    checkDuplicates _e (a:|[]) = ([], Right a)
    checkDuplicates e _ = ([e], Left e)

-- | Dynamic errors

type Dyn e = Components (Either e) (Either e)

mapError
 :: (e -> e')
 -> Components (Either e) (Either e) a
 -> Components (Either e') (Either e') a
mapError f (Components x) =
  Components (bimap (first f) (first f) x)

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
