{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, GeneralizedNewtypeDeriving, TypeOperators #-}
--{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module Goat.Lang.Field
  where

import Goat.Comp
import Goat.Lang.Comment (spaces)
import Goat.Lang.Ident
import Goat.Lang.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Control.Monad (join)
import Data.Bifunctor
import qualified Data.Text as Text
import Data.String (IsString(..))
import Data.Void (Void)


infixl 9 #., :#.

-- | Reference a component of a compound type
class Field_ r where
  type Compound r
  (#.) :: Compound r -> Ident -> r

parseField
 :: Field_ r
 => Parser (Compound r -> r)
parseField = do 
  parseSymbol "."
  i <- parseIdent
  spaces
  return (#. i)

data Field a = a :#. Ident deriving (Eq, Show)

showField :: (a -> ShowS) -> Field a -> ShowS
showField sa (a :#. i) =
  a . showChar ' ' . showSymbol "."
    . showChar ' ' . ident showString i

fromField :: (a -> Compound r) -> Field a -> r
fromField ka (a :#. i) = ka a #. i

fieldProof :: Field a -> Field a
fieldProof = fromField id

instance Field_ (Field a) where
  type Compound (Field a) = a
  a #. i = c :#. i

instance Member Field r => Field_ (Comp r a) where
  type Compound (Comp r a) = Comp r a
  c #. i = join (send (c :#. i))


-- | Nested field accesses
type Chain_ r = (Field_ r, Compound r ~ r)
type Path_ r =
  ( IsString r, Field_ r
  , IsString (Compound r), Chain_ (Compound r)
  )

parsePath
 :: Path_ r => Parser r
parsePath = 
  (do
    s <- parseIdent
    go (fromString s)
      <|> return (fromString s))
    <|> go (fromString "")
  where
    go
      :: (Field_ r, Chain_ (Compound r))
      => Compound r -> Parser r
    go c = do
      f <- parseField
      go (runField (f c))
        <|> return (runField (f c))
    
    runField
     :: Field_ r => Field (Compound r) -> r
    runField = fromField id

showChain
 :: Comp (Field <: t) ShowS -> Comp t ShowS
showChain sc =
  handle (\ a k -> showField id <$> traverse k a)

fromChain
 :: (Field_ r, Compound r ~ r)
 => Comp (Field <: t) r -> Comp t r
fromFieldC =
  handle (\ a k -> fromField id <$> traverse k a)

type SomeChain = Comp (Field <: Null) Void

chainProof :: Comp (Field <: Null) Void -> Comp (Field <: t) a
chainProof = handleAll fromFieldC

type VarChain t = Field <: Var <: t

showVarChain
 :: Comp (VarChain t) ShowS -> Comp t ShowS
showVarChain = showVar . showField

fromVarChain
 :: (Chain_ r, IsString r) => Comp (VarChain t) r -> Comp t r
fromVarChain = fromVar . fromField

type SomeVarChain = Comp (VarChain Null) Void

type Path t = Field SomeVarChain <: Var <: t

newtype SomePath =
  SomePath {
    getPath
     :: forall t a
      . Comp (Field SomeVarChain <: Var <: t) a
    }

instance Field_ SomePath where
  type Compound SomePath = SomeVarChain
  c #. i = SomePath (c #. i)

instance IsString SomePath where
  fromString s = SomePath (fromString s)

showPath
 :: SomePath -> Comp t ShowS
showPath =
  showVar
  . showField (run . showVarChain)
  . getPath

fromPath
 :: Path_ r => SomePath -> Comp t r
fromPath =
  fromVar
  . fromField (run . fromVarChain)
  . getPath

pathProof
 :: SomePath -> SomePath
pathProof = run . fromPath


-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self i = Self | NoSelf i
  deriving (Eq, Show)
  
self :: r -> (i -> r) -> Self i -> r
self ks ki Self = ks
self ks ki (NoSelf i) = ki i

instance IsString i => IsString (Self i) where
  fromString "" = Self
  fromString s = NoSelf (fromString s)
