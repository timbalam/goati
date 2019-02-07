{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts #-}
module Goat.Syntax.Preface
  where

import Goat.Co (Comp, (<:)(), send, inj, handle)
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

data Imports stmt imp = Extern [stmt] imp deriving (Eq, Show)
  
instance Imports_ (Comp (Imports stmt imp <: k) a) where
  type ImportStmt (Comp (Imports stmt imp <: k) a) = stmt
  type Imp (Comp (Imports stmt imp <: k) a) = imp
  extern_ bdy i = send (Extern bdy i)
  
instance Include_ (Comp k a)
 => Include_ (Comp (Imports stmt imp <: k) a) where
  type Inc (Comp (Imports stmt imp <: k) a) = Inc (Comp k a)
  include_ s i = inj (include_ s i)
  
instance Module_ (Comp k a)
 => Module_ (Comp (Imports stmt imp <: k) a) where
  type ModuleStmt (Comp (Imports stmt imp <: k) a) =
    ModuleStmt (Comp k a)
  module_ bdy = inj (module_ bdy)

showImports
 :: (stmt -> ShowS)
 -> (imp -> ShowS)
 -> (Comp k a -> ShowS)
 -> Comp (Imports stmt imp <: k) a -> ShowS
showImports ss si sa = sa . handle (\ (Extend sbdy i) _ ->
  case sbdy of
    [] -> return (si i)
    sbdy -> return (showImports' ss si (Extend sbdy i)))

showImports' ss si sa (Extern sbdy i) =
  showKeyword "extern"
    . showChar '\n'
    . showBody (showChar '\n') ss sbdy
    . showChar '\n'
    . si i

fromImports
 :: Imports_ r
 => (stmt -> ImportStmt r)
 -> (imp -> Imp r)
 -> (Comp k r -> r)
 -> Comp (Imports stmt imp <: k) r -> r
fromImports ss si sa = sa . handle (\ (Extern sbdy i) _ ->
  extern_ (map ss sbdy) (si i))


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

type LetImport klhs lhs krhs rhs k =
  Let (Comp (Ident <: klhs) lhs) (Comp (Text <: krhs) rhs) <: k

showLetImport
 :: (Comp klhs ShowS -> ShowS)
 -> (Comp krhs ShowS -> ShowS)
 -> (Comp k ShowS -> ShowS)
 -> Comp (LetImport klhs ShowS krhs ShowS k) ShowS -> ShowS
showLetImport sl sr = showLet (showIdent sl) (showText sr)

fromLetImport
 :: LetImport_ s
 => (Comp klhs (Lhs s) -> Lhs s)
 -> (Comp krhs (Rhs s) -> Rhs s)
 -> (Comp k s -> s)
 -> Comp (LetImport klhs (Lhs s) krhs (Rhs s) k) s -> s
fromLetImport kl kr = fromLet (fromIdent kl) (fromText kr)

  
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
  
instance Include_ (Comp (Include inc <: k) a) where
  type Inc (Comp (Include inc <: k) a) = inc
  include_ s i = send (Include s i)
  
instance Module_ (Comp k a)
 => Module_ (Comp (Include inc <: k) a) where
  type ModuleStmt (Comp (Include inc <: k) a) =
    ModuleStmt (Comp k a)
  module_ bdy = inj (module_ bdy)
  
showInclude
 :: (inc -> ShowS)
 -> (Comp k a -> ShowS)
 -> Comp (Include inc <: k) ShowS -> ShowS
showInclude si sa = sa . handle (\ i _ ->
  return (showInclude' si i))
  
showInclude' :: (inc -> ShowS) -> Include k a -> ShowS
showInclude' si (Include s i) =
  showKeyword "include" . showChar ' '
    . showIdent runComp (fromString s)
    . showChar '\n'
    . si i

fromInclude
 :: Include_ r
 => (inc -> Inc r)
 -> (Comp k r -> r)
 -> Comp (Include inc <: k) r -> r
fromInclude ki ka = ka . handle (\ (Include s i) _ ->
  return (include_ s (ki i)))


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
 -> (Comp k ShowS -> ShowS)
 -> Comp (Module stmt <: k) ShowS -> ShowS
showModule ss sa = sa . handle (\ (Module bdy) _ ->
  case bdy of
    [] -> id
    bdy -> showModule' ss (Module bdy))

showModule' :: (stmt -> ShowS) -> Module stmt a -> ShowS
showModule' ss (Module sbdy) =
  showKeyword "module"
    . showChar '\n'
    . showBody (showChar '\n') ss sbdy
    . showChar '\n'

fromModule
  :: Module_ r
  => (stmt -> ModuleStmt r)
  -> (Comp k r -> r)
  -> Comp (Module stmt <: k) r -> r
fromModule ks ka = ka . handle (\ (Module sbdy) _ ->
  return (module_ (fmap ks sbdy)))


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
 -> Parser (Imp r)
 -> Parser (Inc r)
 -> Parser r
parsePreface isp msp imp inp =
  (parseImports isp
    <*> (includeOrModule msp inp <|> imp))
    <|> includeOrModule mp inp
    <|> (module_ <$> parseBody mp)
  where
    includeOrModule
     :: ( Include_ r, Module_ (Inc r)
        , Module r, ModuleStmt (Inc r) ~ ModuleStmt r
        )
     => Parser (ModuleStmt r)
     -> Parser (Inc r)
     -> Parser r
    includeOrModule sp inp =
      (parseInclude sp
        <*> (parseModule sp <|> inp))
        <|> parseModule sp


type Preface stmt mstmt kinc inc kimp imp k =
  Imports
    stmt
    (Comp
      (Include (Comp (Module mstmt <: kinc) inc)
        <: Module mstmt
        <: kimp)
      imp)
    <: Include (Comp (Module mstmt <: kinc) inc)
    <: Module mstmt
    <: k

showPreface
 :: (stmt -> ShowS)
 -> (mstmt -> ShowS)
 -> (Comp kinc ShowS ->ShowS)
 -> (imp -> ShowS)
 -> (Comp k ShowS -> ShowS)
 -> Comp (Preface stmt mstmt kinc ShowS kimp ShowS k) ShowS
 -> ShowS
showPreface ss sms sin sim sa =
  showImports
    ss
    (showInclude (showModule sms sin) (showModule sms sim))
    (showInclude (showModule sms sin) (showModule sms sa))

fromPreface
 :: Preface_ p
 => (stmt -> ImportStmt p)
 -> (mstmt -> ModuleStmt p)
 -> (Comp kinc (Inc p) -> Inc p)
 -> (Comp kimp (Imp p) -> Imp p)
 -> (Comp k p -> p)
 -> Comp (Preface stmt mstmt kinc (Inc p) kimp (Imp p) k) p -> p
fromPreface ks kms kin kim ka =
  fromImports
    ks
    (fromInclude (fromModule kms kin) (fromModule kms kim))
    (fromInclude (fromModule kms kin) (fromModule kms ka))
