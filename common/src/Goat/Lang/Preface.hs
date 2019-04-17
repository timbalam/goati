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
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Data.Void (absurd)


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
