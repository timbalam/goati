{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, RankNTypes, FlexibleInstances #-}
module Goat.Lang.Preface
  where

import Goat.Comp
import Goat.Lang.Reflect
import Goat.Lang.Comment (spaces)
import Goat.Lang.Ident
import Goat.Lang.Keyword
import Goat.Lang.Let
import Goat.Lang.Block
import Goat.Lang.Text
import Goat.Lang.Module
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Data.Void (Void)


-- | Import statement (map identifier to a path string)
type LetImport_ s = (Let_ s, IsString (Lhs s), Text_ (Rhs s))

parseLetImport
 :: LetImport_ s => Parser s
parseLetImport = do
  l <- parseIdent
  spaces
  op <- parseLet
  s <- parseText
  return (l `op` s)

type LetImport s t = Let (Var Void) (Text Void) <: t

fromLetImportM
 :: LetImport_ s
 => Comp (LetImport (ImportStmt s) t) s -> Comp t s
fromLetImportM =
  fromLetM (pure . fromVar) (pure . fromText)


-- | IncludeModule
type IncludeModule_ s =
 ( Module_ s, Include_ s, Module_ (Inc s)
 , ModuleStmt s ~ ModuleStmt (Inc s)
 )

parseIncludeModule
 :: IncludeModule_ r
 => Parser (ModuleStmt r)
 -> Parser r
parseIncludeModule sp =
  (parseInclude <*> parseModule sp)
    <|> parseModule sp
    
type IncludeModule s t = Include (Module s Void) <: Module s <: t

fromIncludeModuleM
 :: IncludeModule_ s
 => Comp (IncludeModule (ModuleStmt s) t) s -> Comp t s
fromIncludeModuleM =
  fromModuleM pure . fromIncludeM (fromModule pure)

-- | Proof of 'IncludeModule_ (Comp (IncludeModule s t) a)' instance with 'ModuleStmt (Comp (IncludeModule s t) a) ~ s'
includeModuleProof
 :: Comp (IncludeModule s Null) Void -> Comp (IncludeModule s t) a
includeModuleProof = handleAll fromIncludeModuleM


-- | Module preface can include
-- * an '@import' section with a list of external imports 
-- * an '@include' section with a fall-back module name
-- * an '@module' section with the main module code
type Preface_ r =
  ( IncludeModule_ r, Imports_ r
  , IncludeModule_ (Imp r)
  , ModuleStmt r ~ ModuleStmt (Imp r)
  )

-- | Program preface
parsePreface 
 :: Preface_ r
 => Parser (ImportStmt r)
 -> Parser (ModuleStmt r)
 -> Parser r
parsePreface isp msp =
  (parseImports isp <*> parseIncludeModule msp)
    <|> parseIncludeModule msp
    <|> (module_ <$> parseBody msp)

type Preface is ms t =
  Imports is (Comp (IncludeModule ms Null) Void) <:
    IncludeModule ms t

fromPrefaceM
 :: Preface_ p
 => Comp (Preface (ImportStmt p) (ModuleStmt p) t) p -> Comp t p
fromPrefaceM =
  fromIncludeModuleM
    . fromImportsM pure (handleAll fromIncludeModuleM)

-- | Proof that instance 'Preface_ (Comp (Preface is ms t) a)' exists with 'ModuleStmt (Comp (Preface is ms t) a) ~ ms' and 'ImportStmt (Comp (Preface is ms t) a) ~ is' 
prefaceProof
 :: Comp (Preface is ms Null) Void -> Comp (Preface is ms t) a
prefaceProof = handleAll fromPrefaceM
