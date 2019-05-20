module Goat.Repr.Lang.Preface where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( IDENTIFIER, parseIdentifier
  , TEXTLITERAL, parseTextLiteral
  , INCLUDE, parseInclude
  )
import Goat.Repr.Lang.Pattern
import Goat.Repr.Lang.Expr
import Goat.Repr.Preface
  ( ImportMap, Imports(..), Module )
import Goat.Repr.Pattern
  ( Bindings(..), Declares
  , Decompose, Components, Abs
  , Ident, Inside (..)
  )
import Goat.Repr.Expr
  ( Repr, VarName )
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

proofProgStmt :: PROGSTMT a -> ReadProgStmt a
proofProgStmt = parseProgStmt id

instance Assign_ (ReadProgStmt a) where
  type Lhs (ReadProgStmt a) = ReadPatternPun ReadPattern a
  type Rhs (ReadProgStmt a) = a
  ReadPatternPun (ReadPattern f) (ReadBlock bs) #= a =
    ReadProgStmt (f a `mappend` bs)

-- Include

newtype ReadInclude a =
  ReadInclude {
    readInclude ::
      Include (Abs Components) (Import Ident) (Repr Components) a
    }

proofInclude :: INCLUDE a -> ReadInclude a
proofInclude = parseInclude id 

instance IsList (ReadInclude a) where
  type Item ReadInclude = ReadProgStmt a
  fromList ms =
    ReadInclude
      (Program
        (absFromBindings
          (foldMap readProgStmt ms)
          emptyRepr))
  toList = error "IsList ReadInclude: toList"

instance Include_ (ReadInclude a) where
  type Include (ReadInclude a) = Ident
  include_ k ms = 
    ReadInclude
      (Include
        (Import k)
        (Program
          (absFromBindings
            (foldMap readProgStmt ms)
            emptyRepr)))

-- Imports

newtype ReadImports a =
  ReadImports {
    readImports
     :: Imports FilePath
          (Include (Abs Components (Repr Components) a)
    }

proofImports :: IMPORTS a -> ReadImports a
proofImports = parseImports id

plainInclude :: ReadInclude a -> ReadImports a
plainInclude (ReadInclude (Program f)) =
  ReadImports (Imports mempty (Define f))

instance Module_ ReadImports where
  type ModuleBody ReadImports = ReadInclude
  module_ bdy = plainInclude bdy

instance Extern_ ReadImports where
  type Intern ReadImports = ReadImports
  type ImportItem ReadImports = ReadImportStmt
  extern_ ss (ReadImports (Imports a b)) =
    ReadImports
      (Imports (foldMap readImportStmt ss `mappend` a) b)

-- Preface

newtype ReadPreface =
  ReadPreface {
    readPreface
     :: Imports FilePath
          (Module Components (Repr Components)
            (VarName Void Ident (Import Ident)))
    }

plainImports :: ReadImports -> ReadPreface
plainImports (ReadImports f) = ReadPreface f

instance IsList ReadPreface where
  type Item ReadPreface = ReadProgStmt
  fromList bs = plainImports (module_ bs)
  toList bs = error "IsList ReadPreface: toList"

instance Include_ ReadPreface where
  type Include ReadPreface = Ident
  include_ k bs = plainImports (module_ (include_ k bs))

instance Module_ ReadPreface where
  type ModuleBody ReadPreface = ReadInclude
  module_ bdy = plainImports (module_ bdy)

instance Extern_ ReadPreface where
  type Intern ReadPreface = ReadImports
  type ImportItem ReadPreface = ReadImportStmt
  extern_ ss is = plainImports (extern_ ss is)
  

-- Import statement

newtype ReadImportStmt =
  ReadImportStmt { readImportStmt :: ImportMap FilePath }

instance Assign_ ReadImportStmt where
  type Lhs ReadImportStmt = IDENTIFIER
  type Rhs ReadImportStmt = TEXTLITERAL
  l #= r =
    ReadImportStmt
      (Inside
        (Map.singleton (parseIdentifier l) [parseTextLiteral r]))
