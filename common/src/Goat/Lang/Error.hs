{-# LANGUAGE DeriveFunctor, DeriveFoldable, LambdaCase #-}
-- | This module contains representations for invalid language states
module Goat.Lang.Error 
  ( ImportError(..), displayImportError
  , DefnError(..), displayDefnError
  , ScopeError(..), displayScopeError
  , TypeError(..), displayTypeError
  , displayErrorList
  ) where

import Goat.Lang.Parser
  ( CanonPath, toPath, showPath
  , CanonSelector, toSelector, showSelector
  , IDENTIFIER, showIdentifier
  )
import Data.Foldable (toList)
import Data.List (intersperse, sort)
import qualified Data.Text as Text
import Data.Text (Text)
import Text.Parsec (ParseError)
import System.IO.Error (IOError)


displayErrorList :: (e -> String) -> [e] -> String
displayErrorList displaye es
  = foldMap id
      (intersperse "\n" (map displaye es))

-- Missing import or parse error

data ImportError
  = ParseError ParseError
  | IOError IOError
  deriving (Eq, Show)

displayImportError :: ImportError -> String
displayImportError (ParseError e) = show e
displayImportError (IOError e) = show e

-- | Errors from binding definitions

data DefnError
  = OlappedDeclare [CanonPath]
  | OlappedMatch [CanonSelector]
  | DuplicateImports [IDENTIFIER]
  deriving (Eq, Show)

displayDefnError :: DefnError -> String
displayDefnError
  = \case 
    OlappedDeclare pths
     -> "error: Overlap in declarations: "
     ++ displayErrorList
          ((`showPath` "") . toPath) pths
    
    OlappedMatch sels
     -> "error: Overlap in pattern selectors: "
     ++ displayErrorList
          ((`showSelector` "") . toSelector) sels
    
    DuplicateImports ids
     -> "error: Multiple imports with name: "
     ++ displayErrorList (`showIdentifier` "") ids

-- Unbound identifiers and uses

data ScopeError
  = NotDefinedLocal IDENTIFIER
  | NotDefinedPublic IDENTIFIER
  | NotModule IDENTIFIER
  deriving (Eq, Show)
  
displayScopeError :: ScopeError -> String
displayScopeError (NotDefinedLocal id)
  = "error: No assignment found for name: "
 ++ showIdentifier id ""
displayScopeError (NotDefinedPublic id)
  = "error: No assignment found for name: ."
 ++ showIdentifier id ""
displayScopeError (NotModule id)
  = "error: No module found with name: "
 ++ showIdentifier id ""

-- Type error
 
data TypeError
  = NotComponent IDENTIFIER
  | NotNumber
  | NotText
  | NotBool
  | NoNumberSelf Double
  | NoTextSelf Text
  | NoBoolSelf Bool
  | Hole
  deriving (Eq, Show)
  
displayTypeError :: TypeError -> String
displayTypeError
  = \case
    NotComponent id
     -> "error: No component found with name: "
     ++ showIdentifier id ""
    
    NotNumber
     -> "error: Number expected"

    NotText
     -> "error: Text expected"
    
    NotBool
     -> "error: Bool expected"

    NoNumberSelf d
     -> "error: Component lookup on primitive failed: "
     ++ show d
    
    NoTextSelf t
     -> "error: Component lookup on primitive failed: "
     ++ Text.unpack t
    
    NoBoolSelf b
     -> "error: Component lookup on primitive failed: <bool:"
     ++ if b then "true" else "false"
     ++ ">"
    
    Hole
     -> "error: Program is incomplete"
