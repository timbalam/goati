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
import Data.Bifunctor
import qualified Data.Text as Text
import Data.String (IsString(..))
import Data.Void (Void, absurd)


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

data Field cmp a = cmp :#. Ident
  deriving (Eq, Show)

instance MemberU Field r => Field_ (Comp r a) where
  type Compound (Comp r a) = Dep Field r
  c #. i = send (c :#. i)

showField
 :: (cmp -> ShowS) 
 -> Comp (Field cmp <: t) ShowS -> Comp t ShowS
showField sc = handle (\ (c :#. i) _ ->
  return (showField' (sc c :#. i)))

showField' :: Field ShowS a -> ShowS
showField' (c :#. i) =
  c . showChar ' ' . showSymbol "."
    . showChar ' ' . ident showString i

fromField
 :: Field_ r
 => (cmp -> Compound r)
 -> Comp (Field cmp <: t) r -> Comp t r
fromField kc = handle (\ (c :#. i) _ ->
  return (kc c #. i))

newtype SomeField cmp =
  SomeField { getField :: forall t a . Comp (Field cmp <: t) a }

instance Field_ (SomeField cmp) where
  type Compound (SomeField cmp) = cmp
  c #. i = SomeField (c #. i)

runField
 :: Field_ r
 => SomeField (Compound r) -> r
runField =
  run . fromField id . getField

fieldProof :: SomeField c -> SomeField c
fieldProof = run . fromField id . getField


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

newtype SomeVarChain =
  SomeVarChain {
    getVarChain
     :: forall t a
      . Comp (Field SomeVarChain <: Var <: t) a
    }

instance Field_ SomeVarChain where
  type Compound SomeVarChain = SomeVarChain
  c #. i = SomeVarChain (c #. i)

instance IsString SomeVarChain
  where
    fromString s = SomeVarChain (fromString s)

showVarChain
 :: SomeVarChain -> Comp t ShowS
showVarChain =
  showVar
    . showField (run . showVarChain)
    . getVarChain

fromVarChain
 :: (Chain_ r, IsString r)
 => SomeVarChain -> Comp t r
fromVarChain =
  fromVar
    . fromField (run . fromVarChain)
    . getVarChain

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
