{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts #-}
module Goat.Syntax.Preface
  where

import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident
  ( IsString(..), Ident(..), parseIdent, showIdent, fromIdent )
import Goat.Syntax.Keyword (parseKeyword, showKeyword)
import Goat.Syntax.Let
  ( Let_(..), Let(..), parseLet, showLet, fromLet )
import Goat.Syntax.Block (parseBody, showBody)
import Goat.Syntax.Text
  ( Text_(..), Text(..), parseText, showText, fromText )
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Data.Void (absurd)

-- | Mapping of '@use' names to external module files
data Imports stmt imp a =
    NoImports a
  | Extern [stmt] imp deriving (Eq, Show)

class Imports_ r where
  type ImportStmt r
  type Imp r
  extern_ :: [ImportStmt r] -> Imp r -> r
  
instance Imports_ (Imports stmt imp a) where
  type ImportStmt (Imports stmt imp a) = stmt
  type Imp (Imports stmt imp a) = imp
  extern_ = Extern
  
instance Include_ a => Include_ (Imports stmt imp a) where
  type Inc (Imports stmt imp a) = Inc a
  include_ s inc = NoImports (include_ s inc)
  
instance Module_ a => Module_ (Imports stmt imp a) where
  type ModuleStmt (Imports stmt imp a) = ModuleStmt a
  module_ bdy = NoImports (module_ bdy)


showImports
 :: (stmt -> ShowS)
 -> (imp -> ShowS)
 -> (a -> ShowS)
 -> Imports stmt imp a -> ShowS
showImports ss si sa (NoImports a) = sa a
showImports ss si sa (Extern [] i) = si i
showImports ss si sa (Extern sbdy i) =
  showKeyword "extern"
    . showChar '\n'
    . showBody (showChar '\n') ss sbdy
    . showChar '\n'
    . si i

fromImports
 :: Imports_ r
 => (stmt -> ImportStmt r)
 -> (imp -> Imp r)
 -> (a -> r)
 -> Imports stmt imp a -> r
fromImports ss si sa (NoImports a) = sa a
fromImports ss si sa (Extern sbdy i) = extern_ (map ss sbdy) (si i)
  
parseImports
  :: Imports_ r
  => Parser (ImportStmt r)
  -> Parser (Imp r -> r)
parseImports p = do
  parseKeyword "extern"
  spaces
  xs <- parseBody p
  return (extern_ xs)


-- | Import statement (map identifier to a path string)
type LetImport lhs rhs = Let (Ident lhs) (Text rhs)

type LetImport_ s = (Let_ s, IsString (Lhs s), Text_ (Rhs s))
-- s, Lhs s, Rhs s

showLetImport
 :: (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> (a -> ShowS)
 -> LetImport lhs rhs a -> ShowS
showLetImport sl sr = showLet (showIdent sl) (showText sr)

parseLetImport :: LetImport_ s => Parser s
parseLetImport = do
  l <- parseIdent
  spaces
  op <- parseLet
  s <- parseText
  return (fromString l `op` s)

fromLetImport
 :: LetImport_ s
 => (lhs -> Lhs s)
 -> (rhs -> Rhs s)
 -> (a -> s)
 -> LetImport lhs rhs a -> s
fromLetImport kl kr = fromLet (fromIdent kl) (fromText kr)
  
  
-- | Fall-back module name
data Include inc a =
    NoInclude a
  | Include String inc
  deriving (Eq, Show)

class Include_ r where
  type Inc r
  include_ :: String -> Inc r -> r
  
instance Include_ (Include inc a) where
  type Inc (Include inc a) = inc
  include_ = Include
  
instance Module_ a => Module_ (Include inc a) where
  type ModuleStmt (Include inc a) = ModuleStmt a
  module_ bdy = NoInclude (module_ bdy)
  
showInclude
 :: (inc -> ShowS)
 -> (a -> ShowS)
 -> Include inc a -> ShowS
showInclude si sa (NoInclude a) = sa a
showInclude si sa (Include s i) =
  showKeyword "include" . showChar ' '
    . showIdent absurd (fromString s)
    . showChar '\n'
    . si i
  
parseInclude :: Include_ r => Parser (Inc r -> r)
parseInclude = do
  parseKeyword "include"
  i <- parseIdent
  return (include_ i)

fromInclude
 :: Include_ r
 => (inc -> Inc r)
 -> (a -> r)
 -> Include inc a -> r
fromInclude ki ka (NoInclude a) = ka a
fromInclude ki ka (Include s i) = include_ s (ki i)


-- | Main module code
data Module stmt a =
    NoModule a
  | Module [stmt]
  deriving (Eq, Show)

class Module_ r where
  type ModuleStmt r
  module_ :: [ModuleStmt r] -> r
  
instance Module_ (Module stmt a) where
  type ModuleStmt (Module stmt a) = stmt
  module_ = Module

showModule
 :: (stmt -> ShowS) -> (a -> ShowS) -> Module stmt a -> ShowS
showModule ss sa (NoModule a) = sa a
showModule ss sa (Module []) = id
showMoulde ss sa (Module sbdy) = 
  showKeyword "module"
    . showChar '\n'
    . showBody (showChar '\n') ss sbdy
    . showChar '\n'

parseModule
 :: Module_ r => Parser (ModuleStmt r) -> Parser r
parseModule p = do 
  parseKeyword "module"
  xs <- parseBody p
  return (module_ xs)

fromModule
  :: Module_ r
  => (stmt -> ModuleStmt r)
  -> (a -> r)
  -> Module stmt a -> r
fromModule ks ka (NoModule a) = ka a
fromModule ks ka (Module sbdy) = module_ (fmap ks sbdy)

  

-- | Module preface can include
-- * an '@import' section with a list of external imports 
-- * an '@include' section with a fall-back module name
-- * an '@module' section with the main module code
type Preface stmt mstmt inc imp a =
  Imports
    stmt
    (Include (Module mstmt inc) (Module mstmt imp))
    (Include (Module mstmt inc) (Module mstmt a))

type Preface_ r =
  ( Module_ r, Include_ r, Module_ (Inc r)
  , ModuleStmt (Inc r) ~ ModuleStmt r
  , Imports_ r, Module_ (Imp r)
  , ModuleStmt (Imp r) ~ ModuleStmt r
  , Include_ (Imp r), Inc (Imp r) ~ Inc r
  )
  -- r, ModuleStmt r, Inc r, ModuleStmt (Inc r), Imp r, ModuleStmt (Imp r), Inc (Imp r), ModuleStmt (Inc (Imp r)), ImportStmt r
  
showPreface
 :: (stmt -> ShowS)
 -> (mstmt -> ShowS)
 -> (inc ->ShowS)
 -> (imp -> ShowS)
 -> (a -> ShowS)
 -> Preface stmt mstmt inc imp a -> ShowS
showPreface ss sms sin sim sa =
  showImports
    ss
    (showInclude (showModule sms sin) (showModule sms sim))
    (showInclude (showModule sms sin) (showModule sms sa))

-- | Program preface
parsePreface 
 :: (Preface_ r)
 => Parser (ImportStmt r)
 -> Parser (ModuleStmt r)
 -> Parser r
parsePreface ip mp =
  importsFirst ip mp
    <|> includeFirst mp
    <|> moduleFirst mp
    <|> (module_ <$> parseBody mp)
  where
    importsFirst
     :: ( Imports_ r, Module_ (Imp r)
        , Include_ (Imp r), Module_ (Inc (Imp r))
        , ModuleStmt (Inc (Imp r)) ~ ModuleStmt (Imp r)
        )
     => Parser (ImportStmt r)
     -> Parser (ModuleStmt (Imp r))
     -> Parser r
    importsFirst ip mp = 
      parseImports ip
        <*> (includeFirst mp <|> parseModule mp)
    
    includeFirst
     :: (Include_ r, Module_ (Inc r))
     => Parser (ModuleStmt (Inc r)) -> Parser r
    includeFirst p =
      parseInclude <*> parseModule p
    
    moduleFirst
      :: Module_ r => Parser (ModuleStmt r) -> Parser r
    moduleFirst = parseModule

fromPreface
 :: Preface_ p
 => (stmt -> ImportStmt p)
 -> (mstmt -> ModuleStmt p)
 -> (inc -> Inc p)
 -> (imp -> Imp p)
 -> (a -> p)
 -> Preface stmt mstmt inc imp a -> p
fromPreface ks kms kin kim ka =
  fromImports
    ks
    (fromInclude (fromModule kms kin) (fromModule kms kim))
    (fromInclude (fromModule kms kin) (fromModule kms ka))
