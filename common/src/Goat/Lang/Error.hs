{-# LANGUAGE DeriveFunctor, DeriveFoldable, LambdaCase #-}
-- | This module contains representations for invalid language states
module Goat.Lang.Error 
  ( ImportError(..), displayImportError
  , DefnError(..), displayDefnError
  , ExprCtx(..)
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
  
-- | Source context

data ExprCtx a
  = PathCtx a
  | StmtCtx Int (ExprCtx a)
  | ExtCtx (ExprCtx a)
  deriving (Eq, Ord, Show, Functor, Foldable)

showContextOrder
 :: (Foldable t, Ord (t a))
 => (a -> ShowS)
 -> [t a]
 -> String
showContextOrder showa ctxs
  = foldr
      (\ a s -> showa a ('\n':s))
      ""
      (sort ctxs >>= toList)

-- | Errors from binding definitions

data DefnError
  = OlappedDeclare [ExprCtx CanonPath]
  | OlappedMatch [ExprCtx CanonSelector]
  | DuplicateImports [ExprCtx IDENTIFIER]
  deriving (Eq, Show)

displayDefnError :: DefnError -> String
displayDefnError
  = \case 
    OlappedDeclare ctxs
     -> "error: Overlap in declarations: "
      ++ showContextOrder (showPath . toPath) ctxs
    
    OlappedMatch ctxs
     -> "error: Overlap in pattern selectors: "
     ++ showContextOrder
          (showSelector . toSelector) ctxs
    
    DuplicateImports ctxs
     -> "error: Multiple imports with name: "
     ++ showContextOrder showIdentifier ctxs

-- Unbound identifiers and uses

data ScopeError
  = NotDefinedLocal String
  | NotDefinedPublic String
  | NotModule String
  deriving (Eq, Show)
  
displayScopeError :: ScopeError -> String
displayScopeError (NotDefinedLocal s)
  = "error: No assignment found for name: " ++ s
displayScopeError (NotDefinedPublic s)
  = "error: No assignment found for name: ." ++ s
displayScopeError (NotModule s)
  = "error: No module found with name: " ++ s

-- Type error
 
data TypeError
  = NotComponent String
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
    NotComponent s
     -> "error: No component found with name: " ++ s
    
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
