{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, RankNTypes #-}
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
  , PROGBLOCK, parseProgBlock
  --, CanonPath
  , preface
  )
import Goat.Repr.Lang.Pattern
import Goat.Repr.Lang.Expr
import Goat.Repr.Preface
import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>))
import qualified Data.Map as Map
import Data.Void (Void, absurd)
import Bound ((>>>=))

    
{- 
Program block
-------------

*Program statement*s are equivalent to the *assignment* form of *statement*s.
-}

newtype ReadProgBlock a
  = ReadProgBlock
  { readProgBlock
     :: Bindings
          (AssocViews (Trail Ident))
          (AnnCpts [Trail Ident] Ident)
          (Repr
            (AnnDefns
              [View (Trail Ident)]
              [Trail Ident]
              (AnnCpts [Ident])
              Ident)
            ())
          a
  }

proofProgBlock
 :: PROGBLOCK a -> ReadProgBlock a
proofProgBlock = parseProgBlock id

newtype ReadProgStmt a
  = ReadProgStmt
  { readProgStmt
     :: Bindings
          (AssocViews (Trail Ident))
          (AnnCpts [Trail Ident] Ident)
          (Repr
            (AnnDefns
              [View (Trail Ident)]
              [Trail Ident]
              (AnnCpts [Ident])
              Ident)
            ())
          a
  }

proofProgStmt
 :: PROGSTMT a -> ReadProgStmt a
proofProgStmt = parseProgStmt id

instance IsList (ReadProgBlock a) where
  type Item (ReadProgBlock a) = ReadProgStmt a
  fromList bdy
    = ReadProgBlock (foldMap readProgStmt bdy)
  toList = error "IsList (ReadProgBlock a): toList"

instance
  Assign_ (ReadProgStmt a)
  where
  type Lhs (ReadProgStmt a) = ReadPattern
  type Rhs (ReadProgStmt a) = a
  ReadPattern f #= a = ReadProgStmt (f a)

-- Include

newtype ReadInclude
  = ReadInclude
  { readInclude
     :: Bindings
          Identity
          (AnnDefns
            [View (Trail Ident)]
            [Trail Ident]
            (AnnCpts [Ident])
            Ident)
          (Repr
            (AnnDefns
              [View (Trail Ident)]
              [Trail Ident]
              (AnnCpts [Ident])
              Ident)
            ())
          (VarName Ident Void (Import Ident))
  }

proofInclude :: INCLUDE -> ReadInclude
proofInclude = parseInclude

instance IsList ReadInclude where
  type Item ReadInclude
    = ReadProgStmt (Either Self ReadExpr)
  fromList ms = ReadInclude (Define (pure m))
    where
    m = Repr (Comp (memo e))
    e = Ext
          (abstractBindings
            (transBindings assocShadow
              (readProgBlock (fromList ms))
             >>>= getDefinition))
          emptyRepr
  toList = error "IsList ReadInclude: toList"

instance Include_ ReadInclude where
  type Name ReadInclude = ReadKey
  include_ (ReadKey k) ms
    = ReadInclude (Define (pure m))
    where
    m = Repr (Comp (memo e))
    e = Ext
          (bindDefer
            (Import k)
            (abstractBindings
              (transBindings assocShadow
                (readProgBlock (fromList ms))
               >>>= getDefinition)))
          emptyRepr

-- Imports

newtype ReadImports a
  = ReadImports
  { readImports
     :: Preface (Assocs Ident) FilePath a }

proofImports :: IMPORTS a -> ReadImports a
proofImports = parseImports id

instance Extern_ (ReadImports a) where
  type Intern (ReadImports a) = ReadImports a
  type ImportItem (ReadImports a) = ReadImportStmt
  type ModuleBody (ReadImports a) = a
  extern_ ss (ReadImports (Preface m a))
    = ReadImports
        (Preface
          (foldMap readImportStmt ss `mappend` m)
          a)
  module_ a = ReadImports (Preface mempty a)

-- Preface

newtype ReadPreface
  = ReadPreface
  { readPreface
     :: FilePath
     -> Source
          (Preface
            (Assocs Ident) FilePath ReadInclude)
          (Preface
            (Assocs Ident) FilePath ReadInclude)
  }

proofPreface :: PREFACE -> ReadPreface
proofPreface = parsePreface

instance IsList ReadPreface where
  type Item ReadPreface
    = ReadProgStmt (Either Self ReadExpr)
  fromList bs = module_ (fromList bs)
  toList bs = error "IsList ReadPreface: toList"

instance Include_ ReadPreface where
  type Name ReadPreface = ReadKey
  include_ k bs = module_ (include_ k bs)

instance Extern_ ReadPreface where
  type Intern ReadPreface = ReadImports ReadInclude
  type ImportItem ReadPreface = ReadImportStmt
  type ModuleBody ReadPreface = ReadInclude
  module_ inc = extern_ [] (module_ inc)
  extern_ ss imp
    = case readImports (extern_ ss imp) of
      Preface m a
       -> ReadPreface
            (\ cd
             -> do
                m' <- resolveImports importFile cd m
                return (Preface m' a))
    where
    importFile = sourceFile (readPreface <$> preface)

-- Import statement

newtype ReadTextLiteral
  = ReadTextLiteral { readTextLiteral :: String }

proofTextLiteral :: TEXTLITERAL -> ReadTextLiteral
proofTextLiteral = parseTextLiteral

instance TextLiteral_ ReadTextLiteral where
  quote_ s = ReadTextLiteral s

newtype ReadImportStmt
  = ReadImportStmt
  { readImportStmt :: Assocs Ident FilePath }

proofImportStmt :: IMPORTSTMT -> ReadImportStmt
proofImportStmt = parseImportStmt

instance Assign_ ReadImportStmt where
  type Lhs ReadImportStmt = ReadKey
  type Rhs ReadImportStmt = ReadTextLiteral
  ReadKey l #= ReadTextLiteral fp
    = ReadImportStmt (Assocs [(l, pure fp)])
