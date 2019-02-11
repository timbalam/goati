{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, RankNTypes, FlexibleInstances #-}
module Goat.Syntax.Preface
  where

import Goat.Co
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
class Imports_ r where
  type ImportStmt r
  type Imp r
  extern_ :: [ImportStmt r] -> Imp r -> r

parseImports
  :: Imports_ r
  => Parser (ImportStmt r)
  -> Parser (Imp r -> r)
parseImports p = do
  parseKeyword "extern"
  spaces
  bdy <- parseBody p
  return (extern_ bdy)

data Imports stmt imp a = Extern [stmt] imp deriving (Eq, Show)

instance Imports_ (Comp (Imports stmt imp <: t) a) where
  type ImportStmt (Comp (Imports stmt imp <: t) a) = stmt
  type Imp (Comp (Imports stmt imp <: t) a) = imp
  extern_ bdy i = send (Extern bdy i)
  
instance Include_ (Comp t a)
 => Include_ (Comp (Imports stmt imp <: t) a) where
  type Inc (Comp (Imports stmt imp <: t) a) = Inc (Comp t a)
  include_ s i = inj (include_ s i)
  
instance Module_ (Comp t a)
 => Module_ (Comp (Imports stmt imp <: t) a) where
  type ModuleStmt (Comp (Imports stmt imp <: t) a) =
    ModuleStmt (Comp t a)
  module_ bdy = inj (module_ bdy)

showImports
 :: (stmt -> ShowS)
 -> (imp -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Imports stmt imp <: t) ShowS -> ShowS
showImports ss si st =
  st
  . handle (\ (Extern sbdy i) _ ->
    case sbdy of
      [] -> return (si i)
      sbdy -> return (showImports' ss si (Extern sbdy i)))
  where
    showImports' ss si (Extern sbdy i) =
      showKeyword "extern"
        . showChar '\n'
        . showBody (showChar '\n') ss sbdy
        . showChar '\n'
        . si i

fromImports
 :: Imports_ r
 => (stmt -> ImportStmt r)
 -> (imp -> Imp r)
 -> (Comp t r -> r)
 -> Comp (Imports stmt imp <: t) r -> r
fromImports ss si st =
  st 
  . handle (\ (Extern sbdy i) _ ->
      return (extern_ (map ss sbdy) (si i)))


-- | Import statement (map identifier to a path string)
type LetImport_ s = (Let_ s, IsString (Lhs s), Text_ (Rhs s))
-- s, Lhs s, Rhs s

parseLetImport
 :: LetImport_ s
 => Parser (Lhs s)
 -> Parser (Rhs s)
 -> Parser s
parseLetImport lp rp = do
  l <- parseIdent <|> lp
  spaces
  op <- parseLet
  s <- parseText <|> rp
  return (l `op` s)

type LetImport lhs rhs t =
  Let (lhs (Ident <: Null)) (rhs (Text <: Null)) <: t

showLetImport
 :: (forall e . (Comp e ShowS -> ShowS) -> lhs e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> rhs e -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (LetImport lhs rhs t) ShowS -> ShowS
showLetImport sl sr =
  showLet
    (sl (showIdent runComp))
    (sr (showText runComp))

fromLetImport
 :: LetImport_ s
 => (forall e . (Comp e (Lhs s) -> Lhs s) -> lhs e -> Lhs s)
 -> (forall e . (Comp e (Rhs s) -> Rhs s) -> rhs e -> Rhs s)
 -> (Comp t s -> s)
 -> Comp (LetImport lhs rhs t) s -> s
fromLetImport kl kr =
  fromLet (kl (fromIdent runComp)) (kr (fromText runComp))

  
-- | Fall-back module name
class Include_ r where
  type Inc r
  include_ :: String -> Inc r -> r

parseInclude :: Include_ r => Parser (Inc r -> r)
parseInclude = do
  parseKeyword "include"
  i <- parseIdent
  spaces
  return (include_ i)

data Include inc a = Include String inc deriving (Eq, Show)
  
instance Include_ (Comp (Include inc <: t) a) where
  type Inc (Comp (Include inc <: t) a) = inc
  include_ s i = send (Include s i)
  
instance Module_ (Comp t a)
 => Module_ (Comp (Include inc <: t) a) where
  type ModuleStmt (Comp (Include inc <: t) a) =
    ModuleStmt (Comp t a)
  module_ bdy = inj (module_ bdy)
  
showInclude
 :: (inc -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Include inc <: t) ShowS -> ShowS
showInclude si st =
  st
  . handle (\ i _ -> return (showInclude' si i))
  
showInclude' :: (inc -> ShowS) -> Include inc a -> ShowS
showInclude' si (Include s i) =
  showKeyword "include" . showChar ' '
    . showIdent runComp (fromString s)
    . showChar '\n'
    . si i

fromInclude
 :: Include_ r
 => (inc -> Inc r)
 -> (Comp t r -> r)
 -> Comp (Include inc <: t) r -> r
fromInclude ki kt =
  kt
  . handle (\ (Include s i) _ -> return (include_ s (ki i)))


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

instance Module_ (Comp (Module stmt <: k) a) where
  type ModuleStmt (Comp (Module stmt <: k) a) = stmt
  module_ bdy = send (Module bdy)

showModule
 :: (stmt -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Module stmt <: t) ShowS -> ShowS
showModule ss st =
  st
  . handle (\ (Module bdy) _ ->
      return (case bdy of
        [] -> id
        bdy -> showModule' ss (Module bdy)))

showModule' :: (stmt -> ShowS) -> Module stmt a -> ShowS
showModule' ss (Module sbdy) =
  showKeyword "module"
    . showChar '\n'
    . showBody (showChar '\n') ss sbdy
    . showChar '\n'

fromModule
  :: Module_ r
  => (stmt -> ModuleStmt r)
  -> (Comp t r -> r)
  -> Comp (Module stmt <: t) r -> r
fromModule ks kt =
  kt
  . handle (\ (Module sbdy) _ -> return (module_ (fmap ks sbdy)))


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
  )
  -- r, ModuleStmt r, Inc r, Imp r,  ImportStmt r

-- | Program preface
parsePreface 
 :: Preface_ r
 => Parser (ImportStmt r)
 -> Parser (ModuleStmt r)
 -> Parser r
parsePreface isp msp =
  (parseImports isp <*> includeOrModule msp)
    <|> includeOrModule msp
    <|> (module_ <$> parseBody msp)
  where
    includeOrModule
     :: ( Include_ r, Module_ (Inc r)
        , Module_ r, ModuleStmt (Inc r) ~ ModuleStmt r
        )
     => Parser (ModuleStmt r)
     -> Parser r
    includeOrModule sp =
      (parseInclude <*> parseModule sp)
        <|> parseModule sp


type Preface stmt imp inc mstmt t =
  Imports
    stmt
    (imp
      (Include (inc (Module mstmt <: Null))
        <: Module mstmt
        <: Null))
    <: Include (inc (Module mstmt <: Null))
    <: Module mstmt
    <: t

showPreface
 :: (stmt -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> imp e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> inc e -> ShowS)
 -> (mstmt -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Preface stmt imp inc mstmt t) ShowS -> ShowS
showPreface ss sim sin sms st =
  showImports
    ss
    (sim
      (showInclude
        (sin (showModule sms runComp))
        (showModule sms runComp)))
    (showInclude
      (sin (showModule sms runComp))
      (showModule sms st))

fromPreface
 :: Preface_ p
 => (stmt -> ImportStmt p)
 -> (forall e . (Comp e (Imp p) -> Imp p) -> imp e -> Imp p)
 -> (forall e . (Comp e (Inc p) -> Inc p) -> inc e -> Inc p)
 -> (mstmt -> ModuleStmt p)
 -> (Comp t p -> p)
 -> Comp (Preface stmt imp inc mstmt t) p -> p
fromPreface ks kim kin kms kt =
  fromImports
    ks
    (kim 
      (fromInclude
        (kin (fromModule kms runComp))
        (fromModule kms runComp)))
    (fromInclude
      (kin (fromModule kms runComp))
      (fromModule kms kt))
