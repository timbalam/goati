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
  , PROGBLOCK, parseProgBlock
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
          (Inside (Ambig ((,) [ReprCtx])) Declares)
          (Cpts ((,) [ReprCtx]))
          (Repr (Cpts ((,) [ReprCtx]) ())
          a
  }

proofProgBlock
 :: Selector_ a
 => PROGBLOCK b -> ReadProgBlock (Either a b)
proofProgBlock = parseProgBlock id

newtype ReadProgStmt a
  = ReadProgStmt
  { readProgStmt
     :: (PatternCtx -> ReprCtx)
     -> Bindings
          (Inside (Ambig ((,) [ReprCtx])) Declares) (Cpts ((,) [ReprCtx]))
          (Repr (Cpts (Ambig ((,) [ReprCtx]))) ())
          a
  }

proofProgStmt
 :: Selector_ a
 => PROGSTMT b -> ReadProgStmt (Either a b)
proofProgStmt = parseProgStmt id

instance IsList (ReadProgBlock a) where
  type Item (ReadProgBlock a) = ReadProgStmt a
  fromList bs
    = ReadProgBlock
        (foldMap id
          (mapWithIndex
            (\ i m -> readProgStmt m (StmtCtx i))
            bs)
  toList = error "IsList (ReadProgBlock a): toList"

instance
  Selector_ a
   => Assign_ (ReadProgStmt (Either a b))
  where
  type Lhs (ReadProgStmt (Either a b))
    = ReadPatternPun a b
  type Rhs (ReadProgStmt (Either a b)) = b
  ReadPatternPun (ReadStmt bs) (ReadPattern f) #= b
    = ReadProgStmt
        (\ fc
         -> f (fc . fmap Right)
              (fc . fmap Left)
              (Right b)
              `mappend` bs fc)

-- Include

newtype ReadInclude
  = ReadInclude
  { readInclude
     :: Bindings
          (Cpts ((,) [ReprCtx]))
          (Cpts ((,) [ReprCtx]))
          (Scope (Super Ident)
            (Scope (Public Ident)
              (Repr (Cpts ((,) [ReprCtx])) ())))
          (VarName Void Ident (Import Ident))
  }

proofInclude :: INCLUDE -> ReadInclude
proofInclude = parseInclude

instance IsList ReadInclude where
  type Item ReadInclude
    = ReadProgStmt
        (Either ReadExpr (Either Self ReadExpr))
  fromList ms
    = ReadInclude
        (abstractBindings
          (readProgBlock (fromList ms)
           >>>= either readExpr getDefinition))
  toList = error "IsList ReadInclude: toList"

instance Include_ ReadInclude where
  type Name ReadInclude = Ident
  include_ k ms
    = ReadInclude
        (bindDefer
          (Import k)
          (abstractBindings
            (readProgBlock (fromList ms)
             >>>= either readExpr getDefinition)))

-- Imports

newtype ReadImports a
  = ReadImports { readImports :: Preface FilePath a }

proofImports :: IMPORTS a -> ReadImports a
proofImports = parseImports id

instance Extern_ (ReadImports a) where
  type Intern (ReadImports a) = ReadImports a
  type ImportItem (ReadImports a) = ReadImportStmt
  type ModuleBody (ReadImports a) = a
  extern_ ss (ReadImports (Preface m a))
    = ReadImports
        (Preface
          (foldMap readImportStmt ss `mappend` m) a)
  module_ a = ReadImports (Preface mempty a)

-- Preface

newtype ReadPreface
  = ReadPreface
  { readPreface
     :: FilePath
     -> Source
          (Preface FilePath ReadInclude)
          (Preface FilePath ReadInclude)
  }

proofPreface :: PREFACE -> ReadPreface
proofPreface = parsePreface

instance IsList ReadPreface where
  type Item ReadPreface
    = ReadProgStmt
        (Either ReadExpr (Either Self ReadExpr))
  fromList bs = module_ (fromList bs)
  toList bs = error "IsList ReadPreface: toList"

instance Include_ ReadPreface where
  type Name ReadPreface = Ident
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
  { readImportStmt :: AmbigImports FilePath }

proofImportStmt :: IMPORTSTMT -> ReadImportStmt
proofImportStmt = parseImportStmt

instance Assign_ ReadImportStmt where
  type Lhs ReadImportStmt = IDENTIFIER
  type Rhs ReadImportStmt = ReadTextLiteral
  l #= r
    = ReadImportStmt
        (Inside
          (Map.singleton
            (parseIdentifier l) 
            (pure (readTextLiteral r))))
