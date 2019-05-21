{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
module Goat.Repr.Lang.Preface where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( IDENTIFIER, parseIdentifier
  , TEXTLITERAL, parseTextLiteral
  , INCLUDE, parseInclude
  , PREFACE, parsePreface
  , IMPORTS, parseImports
  , IMPORTSTMT, parseImportStmt
  , PROGSTMT, parseProgStmt
  )
import Goat.Repr.Lang.Pattern
import Goat.Repr.Lang.Expr
import Goat.Repr.Preface
  ( Imports(..), Preface(..), Defer(..) )
import Goat.Repr.Pattern
  ( Bindings(..), Declares
  , Decompose, Components, Abs
  , Ident, Inside (..)
  )
import Goat.Repr.Expr
  ( Repr, VarName, Import(..), emptyRepr
  , absFromBindings
  )
import qualified Data.Map as Map
import Data.Void (Void)

    
{- 
Program
-------

*Module statement*s are equivalent to the *assignment* form of *statement*s.
-}

newtype ReadProgStmt a =
  ReadProgStmt {
    readProgStmt
     :: Bindings Declares Decompose (Repr Components) a
    }

proofProgStmt
 :: Selector_ a => PROGSTMT b -> ReadProgStmt (Either a b)
proofProgStmt = parseProgStmt id

instance Selector_ a => Assign_ (ReadProgStmt (Either a b)) where
  type Lhs (ReadProgStmt (Either a b)) = ReadPatternPun a b
  type Rhs (ReadProgStmt (Either a b)) = b
  ReadPatternPun (ReadStmt bs) (ReadPattern f) #= b =
    ReadProgStmt (f (Right b) `mappend` bs)

-- Include

newtype ReadInclude a =
  ReadInclude {
    readInclude ::
      Defer (Import Ident)
        (Bindings Declares Decompose (Repr Components)
          (Either ReadExpr a)))
    }

proofInclude :: INCLUDE a -> ReadInclude a
proofInclude = parseInclude id


instance IsList (ReadInclude a) where
  type Item (ReadInclude a) = ReadProgStmt (Either ReadExpr a)
  fromList ms =
    ReadInclude (Defer Nothing (foldMap readProgStmt ms))
  toList = error "IsList ReadInclude: toList"

instance Include_ (ReadInclude a) where
  type Include (ReadInclude a) = Ident
  include_ k ms = 
    ReadInclude
      (Defer (Just (Import k))
        (foldMap readProgStmt ms))

-- Imports

newtype ReadImports a =
  ReadImports {
    readImports
     :: Preface FilePath
          (Defer
            (Import Ident) 
            (Bindings Declares Decompose (Repr Components)
              (Either ReadExpr a)))
    }

proofImports :: IMPORTS a -> ReadImports a
proofImports = parseImports id

plainInclude :: ReadInclude a -> ReadImports a
plainInclude (ReadInclude inc) = ReadImports (Preface mempty inc)

instance Module_ (ReadImports a) where
  type ModuleBody (ReadImports a) = ReadInclude a
  module_ bdy = plainInclude bdy

instance Extern_ (ReadImports a) where
  type Intern (ReadImports a) = ReadImports a
  type ImportItem (ReadImports a) = ReadImportStmt
  extern_ ss (ReadImports (Preface a b)) =
    ReadImports
      (Preface (foldMap readImportStmt ss `mappend` a) b)

-- Preface

newtype ReadPreface a =
  ReadPreface {
    readPreface
     :: Preface FilePath
          (Defer (Import Ident)
            (Bindings Declares Decompose (Repr Components)
              (Either ReadExpr a)))
    }

proofPreface :: PREFACE a -> ReadPreface a
proofPreface = parsePreface id

plainImports :: ReadImports a -> ReadPreface a
plainImports (ReadImports f) = ReadPreface f

instance IsList (ReadPreface a) where
  type Item (ReadPreface a) = ReadProgStmt (Either ReadExpr a)
  fromList bs = plainImports (module_ (fromList bs))
  toList bs = error "IsList ReadPreface: toList"

instance Include_ (ReadPreface a) where
  type Include (ReadPreface a) = Ident
  include_ k bs = plainImports (module_ (include_ k bs))

instance Module_ (ReadPreface a) where
  type ModuleBody (ReadPreface a) = ReadInclude a
  module_ bdy = plainImports (module_ bdy)

instance Extern_ (ReadPreface a) where
  type Intern (ReadPreface a) = ReadImports a
  type ImportItem (ReadPreface a) = ReadImportStmt
  extern_ ss is = plainImports (extern_ ss is)
  

-- Import statement

newtype ReadTextLiteral =
  ReadTextLiteral { readTextLiteral :: String }

proofTextLiteral :: TEXTLITERAL -> ReadTextLiteral
proofTextLiteral = parseTextLiteral

instance TextLiteral_ ReadTextLiteral where
  quote_ s = ReadTextLiteral s

newtype ReadImportStmt =
  ReadImportStmt { readImportStmt :: Imports FilePath }

proofImportStmt :: IMPORTSTMT -> ReadImportStmt
proofImportStmt = parseImportStmt

instance Assign_ ReadImportStmt where
  type Lhs ReadImportStmt = IDENTIFIER
  type Rhs ReadImportStmt = ReadTextLiteral
  l #= r =
    ReadImportStmt
      (Inside
        (Map.singleton (parseIdentifier l) [readTextLiteral r]))
