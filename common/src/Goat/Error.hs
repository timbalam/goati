-- | This module contains the language dynamic and static exception machinery.
module Goat.Error 
  ( ImportError(..), displayImportError
  , DefnError(..), displayDefnError
  , ScopeError(..), displayScopeError
  , TypeError(..), displayTypeError
  , StaticError(..), displayStaticError, projectDefnError
  , DynError(..), displayDynError
  , displayErrorList
  ) where

import Data.List (intersperse)
import qualified Data.Text as Text
import Data.Text (Text)
import Text.Parsec (ParseError)
import System.IO.Error (IOError)


displayErrorList :: (e -> String) -> [e] -> String
displayErrorList displaye es =
  foldMap id
    (intersperse "\n" (map displaye es))

-- | Dynamic exception
data DynError =
    StaticError StaticError
  | TypeError TypeError
  deriving (Eq, Show)

displayDynError :: DynError -> String
displayDynError (StaticError e) = displayStaticError e
displayDynError (TypeError e)   = displayTypeError e
displayDynError _               = "unknown error"

data StaticError =
    DefnError DefnError
  | ScopeError ScopeError
  | ImportError ImportError
  deriving (Eq, Show)
  
displayStaticError :: StaticError -> String
displayStaticError (DefnError e)  = displayDefnError e
displayStaticError (ScopeError e) = displayScopeError e
displayStaticError (ImportError e) = displayImportError e

projectDefnError :: StaticError -> Maybe DefnError
projectDefnError (DefnError de) = Just de
projectDefnError _ = Nothing

-- Missing import or parse error

data ImportError = ParseError ParseError | IOError IOError
  deriving (Eq, Show)

displayImportError :: ImportError -> String
displayImportError (ParseError e) = show e
displayImportError (IOError e) = show e

-- | Errors from binding definitions

data DefnError =
    OlappedMatch String
    -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet String
    -- ^ Error if a group assigns to non-disjoint paths
  | DuplicateImport String
    -- ^ Error if an import name is duplicated
  deriving (Eq, Show)
  
displayDefnError :: DefnError -> String
displayDefnError (OlappedMatch s) =
  "error: Multiple component matches for name: " ++ s
displayDefnError (OlappedSet s) =
  "error: Multiple assignments for name: " ++ s
displayDefnError (DuplicateImport s) =
  "error: Multiple imports with name: " ++ s

-- Unbound identifiers and uses
 
data ScopeError =
    NotDefinedLocal String
  | NotDefinedPublic String
  | NotModule String
  deriving (Eq, Show)
  
displayScopeError :: ScopeError -> String
displayScopeError (NotDefinedLocal s) =
  "error: No assignment found for name: " ++ s
displayScopeError (NotDefinedPublic s) =
  "error: No assignment found for name: ." ++ s
displayScopeError (NotModule s) =
  "error: No module found with name: " ++ s

-- Type error
 
data TypeError =
    NotComponent String
  | NotNumber
  | NotText
  | NotBool
  | NoNumberSelf Double
  | NoTextSelf Text
  | NoBoolSelf Bool
  | Hole
  deriving (Eq, Show)
  
displayTypeError :: TypeError -> String
displayTypeError (NotComponent s) =
  "error: No component found with name: " ++ s
displayTypeError NotNumber =
  "error: Number expected"
displayTypeError NotText =
  "error: Text expected"
displayTypeError NotBool =
  "error: Bool expected"
displayTypeError (NoNumberSelf d) =
  "error: Component lookup on primitive failed: " ++ show d
displayTypeError (NoTextSelf t) =
  "error: Component lookup on primitive failed: " ++ Text.unpack t
displayTypeError (NoBoolSelf b) =
  "error: Component lookup on primitive failed: <bool:" ++
    if b then "true" else "false" ++
    ">"
displayTypeError Hole =
  "error: Program is incomplete"
