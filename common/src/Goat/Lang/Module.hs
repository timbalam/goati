{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module Goat.Lang.Module
  where

import Goat.Comp
import Goat.Lang.Comment (spaces)
import Goat.Lang.Keyword
import Goat.Lang.Ident
import Goat.Lang.Block
import Goat.Util ((<&>))
import Control.Applicative (liftA2)
import Text.Parsec.Text (Parser)
  
-- | Mapping of '@use' names to external module files
class Imports_ r where
  type ImportStmt r
  type Imp r
  extern_ :: [ImportStmt r] -> Imp r -> r

parseImports
  :: Imports_ r
  => Parser (ImportStmt r) -> Parser (Imp r -> r)
parseImports p = do
  parseKeyword "extern"
  spaces
  bdy <- parseBody p
  return (extern_ bdy)

data Imports stmt imp a = Extern [stmt] imp deriving (Eq, Show)

showImports
 :: Applicative m
 => (stmt -> m ShowS)
 -> (imp -> m ShowS)
 -> Imports stmt imp a -> m ShowS
showImports ss si (Extern sbdy i) =
  case sbdy of
    [] -> si i
    sbdy ->
      liftA2 showImports' (showBody (showChar '\n') ss sbdy) (si i)
  where
    showImports' s i =
      showKeyword "extern" .
        showChar '\n' .
        s .
        showChar '\n' .
        i

fromImports
 :: (Applicative m, Imports_ r)
 => (stmt -> m (ImportStmt r))
 -> (imp -> m (Imp r))
 -> Imports stmt imp a -> m r
fromImports ks ki (Extern sbdy i) =
  liftA2 extern_ (traverse ks sbdy) (ki i)

instance Imports_ (Imports is i a) where
  type ImportStmt (Imports is i a) = is
  type Imp (Imports is i a) = i
  extern_ = Extern

instance MemberU2 Imports r => Imports_ (Comp r a) where
  type ImportStmt (Comp r a) = U2Index Imports r
  type Imp (Comp r a) = U1Index Imports r
  extern_ bdy i = send (Extern bdy i)

  
-- | Fall-back module name
class Include_ r where
  type Inc r
  include_ :: Ident -> Inc r -> r

parseInclude :: Include_ r => Parser (Inc r -> r)
parseInclude = do
  parseKeyword "include"
  i <- parseIdent
  spaces
  return (include_ i)

data Include inc a = Include Ident inc deriving (Eq, Show)

showInclude
 :: Functor m => (inc -> m ShowS) -> Include inc a -> m ShowS
showInclude si (Include s i) =
  si i <&> \ i ->
    showKeyword "include" .
      showChar ' ' .
      ident showString s .
      showChar '\n' .
      i

fromInclude
 :: (Functor m, Include_ r)
 => (inc -> m (Inc r)) -> Include inc a -> m r
fromInclude ki (Include s i) = include_ s <$> ki i

instance Include_ (Include inc a) where
  type Inc (Include inc a) = inc
  include_ = Include
 
instance MemberU Include r => Include_ (Comp r a) where
  type Inc (Comp r a) = UIndex Include r
  include_ s i = send (Include s i)


-- | Main module code
class Module_ r where
  type ModuleStmt r
  module_ :: [ModuleStmt r] -> r

parseModule
 :: Module_ r => Parser (ModuleStmt r) -> Parser r
parseModule p = do 
  parseKeyword "module"
  xs <- parseBody p
  return (module_ xs)

data Module stmt a = Module [stmt] deriving (Eq, Show)

showModule
 :: Applicative m
 => (stmt -> m ShowS) -> Module stmt a -> m ShowS
showModule ss (Module bdy) = case bdy of
  [] -> pure id
  bdy -> showModule' <$> showBody (showChar '\n') ss bdy
  where
    showModule' s =
      showKeyword "module" .
        showChar '\n' .
        s .
        showChar '\n'

fromModule
  :: (Applicative m, Module_ r)
  => (stmt -> m (ModuleStmt r)) -> Module stmt a -> m r
fromModule ks (Module sbdy) = module_ <$> traverse ks sbdy

instance Module_ (Module ms a) where
  type ModuleStmt (Module ms a) = ms
  module_ = Module

instance MemberU Module r => Module_ (Comp r a) where
  type ModuleStmt (Comp r a) = UIndex Module r
  module_ bdy = send (Module bdy)
