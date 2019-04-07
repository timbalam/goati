{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, RankNTypes, FlexibleInstances #-}
module Goat.Lang.Preface
  where

import Goat.Comp
import Goat.Lang.Comment (spaces)
import Goat.Lang.Ident
import Goat.Lang.Keyword
import Goat.Lang.Let
import Goat.Lang.Block
import Goat.Lang.Text
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

instance MemberU2 Imports r => Imports_ (Comp r a) where
  type ImportStmt (Comp r a) = Dep1 Imports r
  type Imp (Comp r a) = Dep2 Imports r
  extern_ bdy i = send (Extern bdy i)

showImports
 :: (stmt -> ShowS)
 -> (imp -> ShowS)
 -> Comp (Imports stmt imp <: t) ShowS -> Comp t ShowS
showImports ss si =
  handle
    (\ (Extern sbdy i) _ ->
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
 -> Comp (Imports stmt imp <: t) r -> Comp t r
fromImports ss si =
  handle
    (\ (Extern sbdy i) _ ->
      return (extern_ (map ss sbdy) (si i)))


-- | Import statement (map identifier to a path string)
type LetImport_ s = (Let_ s, IsString (Lhs s), Text_ (Rhs s))
-- s, Lhs s, Rhs s

parseLetImport
 :: LetImport_ s => Parser s
parseLetImport = do
  l <- parseIdent
  spaces
  op <- parseLet
  s <- parseText
  return (l `op` s)

newtype SomeLetImport =
  SomeLetImport {
    getLetImport
     :: forall t a 
      . Comp (Let SomeVar SomeText <: t) a
    }

instance Let_ SomeLetImport where
  type Lhs SomeLetImport = SomeVar
  type Rhs SomeLetImport = SomeText
  l #= r = SomeLetImport (l #= r)

showLetImport
 :: SomeLetImport -> Comp t ShowS
showLetImport =
  showLet
    (run . showVar . getVar)
    (run . showText . getText)
    . getLetImport

fromLetImport
 :: LetImport_ s
 => SomeLetImport -> Comp t s
fromLetImport =
  fromLet
    (run . fromVar . getVar)
    (run . fromText . getText)
    . getLetImport

  
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
  
instance MemberU Include r => Include_ (Comp r a) where
  type Inc (Comp r a) = Dep Include r
  include_ s i = send (Include s i)
  
showInclude
 :: (inc -> ShowS)
 -> Comp (Include inc <: t) ShowS -> Comp t ShowS
showInclude si =
  handle (\ i _ -> return (showInclude' si i))
  
showInclude' :: (inc -> ShowS) -> Include inc a -> ShowS
showInclude' si (Include s i) =
  showKeyword "include" . showChar ' '
    . ident showString s
    . showChar '\n'
    . si i

fromInclude
 :: Include_ r
 => (inc -> Inc r)
 -> Comp (Include inc <: t) r -> Comp t r
fromInclude ki =
  handle (\ (Include s i) _ -> return (include_ s (ki i)))


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

instance MemberU Module r => Module_ (Comp r a) where
  type ModuleStmt (Comp r a) = Dep Module r
  module_ bdy = send (Module bdy)

showModule
 :: (stmt -> ShowS)
 -> Comp (Module stmt <: t) ShowS -> Comp t ShowS
showModule ss =
  handle
    (\ (Module bdy) _ ->
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
  -> Comp (Module stmt <: t) r -> Comp t r
fromModule ks =
  handle (\ (Module sbdy) _ -> return (module_ (fmap ks sbdy)))
        
newtype SomeModule stmt =
  SomeModule {
    getModule :: forall t a . Comp (Module stmt <: t) a
    }

instance Module_ (SomeModule stmt) where
  type ModuleStmt (SomeModule stmt) = stmt
  module_ bdy = SomeModule (module_ bdy)

moduleProof :: SomeModule stmt -> SomeModule stmt
moduleProof = run . fromModule id . getModule

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
    
newtype SomeIncludeModule stmt =
  SomeIncludeModule {
    getIncludeModule
     :: forall t a
      . Comp
          (Include (SomeModule stmt) <:
          Module stmt <:
          t)
          a
    }

instance Include_ (SomeIncludeModule stmt) where
  type Inc (SomeIncludeModule stmt) = SomeModule stmt
  include_ s i = SomeIncludeModule (include_ s i)

instance Module_ (SomeIncludeModule stmt) where
  type ModuleStmt (SomeIncludeModule stmt) = stmt
  module_ bdy = SomeIncludeModule (module_ bdy)

showIncludeModule
 :: (stmt -> ShowS)
 -> SomeIncludeModule stmt -> Comp t ShowS
showIncludeModule ss =
  showModule ss
    . showInclude (run . showModule ss . getModule)
    . getIncludeModule

fromIncludeModule
 :: IncludeModule_ s
 => (stmt -> ModuleStmt s)
 -> SomeIncludeModule stmt -> Comp t s
fromIncludeModule ks =
  fromModule ks
    . fromInclude (run . fromModule ks . getModule)
    . getIncludeModule

includeModuleProof
 :: SomeIncludeModule s -> SomeIncludeModule s
includeModuleProof = run . fromIncludeModule id

-- | Module preface can include
-- * an '@import' section with a list of external imports 
-- * an '@include' section with a fall-back module name
-- * an '@module' section with the main module code
type Preface_ r =
  ( IncludeModule_ r, Imports_ r
  , IncludeModule_ (Imp r)
  , ModuleStmt r ~ ModuleStmt (Imp r)
  )
  -- r, ModuleStmt r, Inc r, Imp r,  ImportStmt r

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
    
newtype SomePreface istmt mstmt =
  SomePreface {
    getPreface
     :: forall t a
      . Comp
          (Imports
            istmt
            (SomeIncludeModule mstmt) <:
          Include (SomeModule mstmt) <:
          Module mstmt <:
          t)
          a
    }
    
instance Module_ (SomePreface istmt mstmt) where
  type ModuleStmt (SomePreface istmt mstmt) = mstmt
  module_ bdy = SomePreface (module_ bdy)

instance Imports_ (SomePreface istmt mstmt) where
  type ImportStmt (SomePreface istmt mstmt) = istmt
  type Imp (SomePreface istmt mstmt) =
    SomeIncludeModule mstmt
  extern_ bdy i = SomePreface (extern_ bdy i)

instance Include_ (SomePreface istmt mstmt) where
  type Inc (SomePreface istmt mstmt) = SomeModule mstmt
  include_ s i = SomePreface (include_ s i)

showPreface
 :: (istmt -> ShowS)
 -> (mstmt -> ShowS)
 -> SomePreface istmt mstmt -> Comp t ShowS
showPreface sis sms =
  showModule sms
    . showInclude (run . showModule sms . getModule)
    . showImports
        sis
        (run . showIncludeModule sms)
    . getPreface

fromPreface
 :: Preface_ p
 => (istmt -> ImportStmt p)
 -> (mstmt -> ModuleStmt p)
 -> SomePreface istmt mstmt -> Comp t p
fromPreface kis kms =
  fromModule kms
    . fromInclude (run . fromModule kms . getModule)
    . fromImports
        kis
        (run . fromIncludeModule kms)
    . getPreface

prefaceProof
 :: SomePreface is ms -> SomePreface is ms
prefaceProof = run . fromPreface id id