{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts #-}
module Goat.Syntax.Preface
  where

import Goat.Syntax.Ident (Ident(..), parseIdent, showIdent)
import Goat.Syntax.Keyword (parseKeyword, showKeyword)
import Goat.Syntax.Let (Let_(..), parseLet, showLet)
import Goat.Syntax.Block (parseBody, showBody)
import Goat.Syntax.Text (Text_(..), parseText, showText)
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Data.String (IsString(..))

-- | Mapping of '@use' names to external module files
data Imports s a = Extern [s] a deriving (Eq, Show)

class Imports_ r where
  type ImportStmt r
  type Imp r
  extern_ :: [ImportStmt r] -> Imp r -> r
  
instance Imports_ (Imports s a) where
  type ImportStmt (Imports s a) = s
  type Imp (Imports s a) = a
  extern_ = Extern
  
parseImports
  :: Imports_ r
  => Parser (ImportStmt r)
  -> Parser (Imp r -> r)
parseImports p = do
  parseKeyword "extern"
  xs <- parseBody p
  return (extern_ xs)

showImports
 :: (s -> ShowS) -> (a -> ShowS) -> Imports s a -> ShowS
showImports sx sa (Extern [] a) = sa a
showImports sx sa (Extern xs a) =
  showKeyword "extern"
    . showChar '\n'
    . showBody (showChar '\n') sx xs
    . showChar '\n'
    . sa a

fromImports
 :: Imports_ r
 => (s -> ImportStmt r)
 -> (a -> Imp r)
 -> Imports s a -> r
fromImports sx sa (Extern xs a) = extern_ (map sx xs) (sa a)


-- | Import statement (map identifier to a path string)
type LetImport_ s = (Let_ s, IsString (Lhs s), IsString (Rhs s))

parseLetImport :: LetImport_ s => Parser s
parseLetImport = do
  Ident i <- parseIdent
  op <- parseLet 
  s <- parseText
  return (op (fromString i) s)
  
  
-- | Fall-back module name
data Include a = Include Ident a deriving (Eq, Show)

class Include_ r where
  type Inc r
  include_ :: Ident -> Inc r -> r
  
instance Include_ (Include a) where
  type Inc (Include a) = a
  include_ = Include
  
parseInclude :: Include_ r => Parser (Inc r -> r)
parseInclude = do
  parseKeyword "include"
  i <- parseIdent
  return (include_ i)
  
showInclude :: (a -> ShowS) -> Include a -> ShowS
showInclude sa (Include i a) =
  showKeyword "include" . showChar ' ' . showIdent i
    . showChar '\n'
    . sa a

fromInclude :: Include_ r => (a -> Inc r) -> Include a -> r
fromInclude ka (Include i a) = include_ i (ka a)
  
-- | Main module code
data Module s = Module [s] deriving (Eq, Show)

class Module_ r where
  type ModuleStmt r
  module_ :: [ModuleStmt r] -> r
  
instance Module_ (Module s) where
  type ModuleStmt (Module s) = s
  module_ = Module
  
parseModule
 :: Module_ r => Parser (ModuleStmt r) -> Parser r
parseModule p = do 
  parseKeyword "module"
  xs <- parseBody p
  return (module_ xs)

showModule :: (s -> ShowS) -> Module s -> ShowS
showModule sx (Module []) = id
showMoulde sx (Module xs) = 
  showKeyword "module"
    . showChar '\n'
    . showBody (showChar '\n') sx xs
    . showChar '\n'

  

-- | Module preface can include
-- * an '@import' section with a list of external imports 
-- * an '@include' section with a fall-back module name
-- * an '@module' section with the main module code
type Preface_ r =
  ( Module_ r, Include_ r, Module_ (Inc r)
  , ModuleStmt (Inc r) ~ ModuleStmt r
  , Imports_ r, Module_ (Imp r)
  , ModuleStmt (Imp r) ~ ModuleStmt r
  , Include_ (Imp r), Inc (Imp r) ~ Inc r
  , Module_ (Inc (Imp r))
  )


-- | Program preface
parsePreface 
 :: (Preface_ r, LetImport_ (ImportStmt r))
 => Parser (ModuleStmt r) -> Parser r
parsePreface p =
  importsFirst p
    <|> includeFirst p
    <|> moduleFirst p
    <|> (module_ <$> parseBody p)
  where
    importsFirst
     :: ( Imports_ r, LetImport_ (ImportStmt r)
        , Module_ (Imp r), Include_ (Imp r)
        , Module_ (Inc (Imp r))
        , ModuleStmt (Inc (Imp r)) ~ ModuleStmt (Imp r)
        )
     => Parser (ModuleStmt (Imp r)) -> Parser r
    importsFirst p = 
      parseImports
        parseLetImport
        <*> (includeFirst p <|> parseModule p)
    
    includeFirst
     :: (Include_ r, Module_ (Inc r))
     => Parser (ModuleStmt (Inc r)) -> Parser r
    includeFirst p =
      parseInclude <*> parseModule p
    
    moduleFirst
      :: Module_ r => Parser (ModuleStmt r) -> Parser r
    moduleFirst = parseModule