{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, GeneralizedNewtypeDeriving, TypeOperators #-}
--{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module Goat.Syntax.Field
  where

import Goat.Co
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident
  ( Ident(..), parseIdent, fromIdent, showIdent )
import Goat.Syntax.Symbol (parseSymbol, showSymbol)
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
  (#.) :: Compound r -> String -> r

parseField
 :: Field_ r
 => Parser (Compound r -> r)
parseField = do 
  parseSymbol "."
  i <- parseIdent
  spaces
  return (#. i)

data Field cmp a = cmp :#. String
  deriving (Eq, Show)

instance Field_ (Comp (Field cmp <: t) a) where
  type Compound (Comp (Field cmp <: t) a) = cmp
  c #. i = send (c :#. i)

instance
  IsString (Comp t a) => IsString (Comp (Field cmp <: t) a)
  where
    fromString s = inj (fromString s)

instance
  Field_ (Comp t a) => Field_ (Comp (Ident <: t) a)
  where
    type Compound (Comp (Ident <: t) a) = Compound (Comp t a)
    c #. i = inj (c #. i)

instance
  Field_ (Comp t a) => Field_ (Comp (Self <: t) a)
  where
    type Compound (Comp (Self <: t) a) = Compound (Comp t a)
    c #. i = inj (c #. i)

showField
 :: (cmp -> ShowS) 
 -> Comp (Field cmp <: t) ShowS -> Comp t ShowS
showField sc = handle (\ (c :#. i) _ ->
  return (showField' (sc c :#. i)))

showField' :: Field ShowS a -> ShowS
showField' (c :#. i) =
  c . showChar ' ' . showSymbol "."
    . showChar ' ' . run (showIdent (fromString i))

fromField
 :: Field_ r
 => (cmp -> Compound r)
 -> Comp (Field cmp <: t) r -> Comp t r
fromField kc = handle (\ (c :#. i) _ ->
  return (kc c #. i))

newtype SomeField cmp =
  SomeField {
    getField :: forall t a . Comp (Field cmp <: t) a
    }

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

newtype SomeStringChain =
  SomeStringChain {
    getStringChain
      :: forall t a
       . Comp (Field SomeStringChain <: Self <: Ident <: t) a
    }

instance Field_ SomeStringChain where
  type Compound SomeStringChain = SomeStringChain
  c #. i = SomeStringChain (c #. i)

instance IsString SomeStringChain
  where
    fromString s = SomeStringChain (fromString s)

showStringChain :: SomeStringChain -> Comp t ShowS
showStringChain =
  showIdent
    . showSelf
    . showField (run . showStringChain)
    . getStringChain

fromStringChain
 :: (Chain_ r, IsString r) => SomeStringChain -> Comp t r
fromStringChain =
  fromIdent
    . fromSelf
    . fromField (run . fromStringChain)
    . getStringChain

newtype SomePath =
  SomePath {
    getPath
      :: forall t a . Comp (Field SomeStringChain <: Ident <: t) a
    }

instance Field_ SomePath where
  type Compound SomePath = SomeStringChain
  c #. i = SomePath (c #. i)

instance IsString SomePath where
  fromString s = SomePath (fromString s)

showPath
 :: SomePath -> Comp t ShowS
showPath =
  showIdent 
  . showField (run . showStringChain)
  . getPath
  
fromPath
 :: Path_ r => SomePath -> Comp t r
fromPath =
  fromIdent
  . fromField (run . fromStringChain)
  . getPath

pathProof
 :: SomePath -> SomePath
pathProof = run . fromPath


-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self a = Self deriving (Eq, Show)

instance IsString (Comp t a)
  => IsString (Comp (Self <: t) a) where
  fromString "" = send Self
  fromString s = inj (fromString s)

showSelf
 :: Comp (Self <: t) ShowS -> Comp t ShowS
showSelf = handle (\ _ _ -> return id)

fromSelf
 :: IsString r => Comp (Self <: t) r -> Comp t r
fromSelf = handle (\ _ _ -> return (fromString ""))
