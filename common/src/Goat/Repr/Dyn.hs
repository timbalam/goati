{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

-- | This module implements some data types and definitions for represent Goat values that track errors dynamically.
-- It defines a data type 'Dyn': a wrapper for injecting dynamic errors inside a storage type.

module Goat.Repr.Dyn where

import Goat.Repr.Pattern
  ( Extend(..), Components(..), Ident, showIdent
  , Identity(..), Text, Local(..), Public(..)
  )
import Goat.Repr.Expr (VarName, Import(..))
import Goat.Util ((<&>))
import Data.Bifunctor (bimap, first)
import Data.Bitraversable (bitraverse)
import Data.Foldable (traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Data.Void (Void)


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

checkVar
 :: (ScopeError -> e)
 -> VarName Ident Ident (Import Ident)
 -> ([e], Components (Either e) (Either e) a)
checkVar throwe n = ([e], throwDyn e)
  where
    e =
      case n of
        Left (Public n) -> throwe (NotDefinedPublic n)
        Right (Left (Local n)) -> throwe (NotDefinedLocal n)
        Right (Right (Import n)) -> throwe (NotModule n)

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
    ([], Left e)  -> "<" ++ showe e ++ ">"
    (ks, ev)      -> "<components: "
      ++ show (map showIdent ks)
      ++ ", "
      ++ either showe showa ev
      ++ ">"

-- Unbound identifiers and uses
 
data ScopeError =
    NotDefinedLocal Ident
  | NotDefinedPublic Ident
  | NotModule Ident
  deriving (Eq, Show)
  
displayScopeError :: ScopeError -> String
displayScopeError (NotDefinedLocal i) =
  "error: No assignment found for name: " ++ showIdent i
displayScopeError (NotDefinedPublic i) =
  "error: No assignment found for name: ." ++ showIdent i
displayScopeError (NotModule i) =
  "error: No module found with name: " ++ showIdent i


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
  "error: Multiple component matches for name: " ++ showIdent i
displayDefnError (OlappedSet i) =
  "error: Multiple assignments for name: " ++ showIdent i
displayDefnError (DuplicateImport i) =
  "error: Multiple imports with name: " ++ showIdent i
