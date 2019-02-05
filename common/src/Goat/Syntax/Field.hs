{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, GeneralizedNewtypeDeriving, TypeOperators #-}
--{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module Goat.Syntax.Field
  where

import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident
  ( Ident(..), parseIdent, fromIdent, showIdent )
import Goat.Syntax.Symbol (parseSymbol, showSymbol)
import Goat.Co
  ( Comp(..), (<:)(..), Null, runComp, inj, send, handle )
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
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

instance Field_ (Comp (Field cmp <: k) a) where
  type Compound (Comp (Field cmp <: k) a) = cmp
  c #. i = send (c :#. i)

instance IsString (Comp k a)
 => IsString (Comp (Field cmp <: k) a) where
  fromString s = inj (fromString s)

showField
 :: (cmp -> ShowS)
 -> Comp (Field cmp <: k) ShowS -> Comp k ShowS
showField sc = handle (\ f _ -> return (showField' sc f))

showField' :: (cmp -> ShowS) -> Field cmp a -> ShowS
showField' sc (c :#. i) =
  sc c . showChar ' ' . showSymbol "."
    . showChar ' ' . runComp (showIdent (fromString i))

fromField
 :: Field_ r
 => (cmp -> Compound r)
 -> Comp (Field cmp <: k) r -> Comp k r
fromField kc =
  handle (\ (c :#. i) _ -> return (fromField' kc (c :#. i)))

fromField'
 :: Field_ r => (cmp -> Compound r) -> Field cmp a -> r
fromField' kc (c :#. i) = kc c #. i


-- | Nested field accesses
type Chain_ r = (Field_ r, Compound r ~ r)
type Path_ r = (Field_ r, Chain_ (Compound r))

parsePath
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> r)
parsePath = go id
  where
    go
      :: (Field_ r, Chain_ (Compound r))
      => (Compound r -> Compound r)
      -> Parser (Compound r -> r)
    go k = do
      f <- parseField
      (go (runPath . f . k)
        <|> return (runPath . f . k))
  
    runPath
     :: (Field_ r, Chain_ (Compound r))
     => Comp (Field (Compound r) <: Null) Void -> r
    runPath m =
      runComp (fromField id (fmap absurd m))


newtype Chain a = Chain (Field a a) deriving (Eq, Show)
type Path kcmp cmp = Field (Comp (Chain <: kcmp) cmp)

instance Field_ (Comp (Chain <: k) a) where
  type Compound (Comp (Chain <: k) a) = Comp (Chain <: k) a
  c #. i = send (Chain (c :#. i))

showChain :: Comp (Chain <: k) ShowS -> Comp k ShowS
showChain = handle (\ (Chain (c :#. i)) k -> do
  c' <- k c
  return (showField' id (c' :#. i)))

showPath
 :: (Comp kcmp ShowS -> ShowS)
 -> Comp (Path kcmp ShowS <: k) ShowS -> Comp k ShowS
showPath sc = showField (sc . showChain)

fromChain :: Chain_ r => Comp (Chain <: k) r -> Comp k r
fromChain = handle (\ (Chain (c :#. i)) k -> do
  c' <- k c
  return (fromField' id (c' :#. i)))

fromPath
 :: Path_ r
 => (Comp kcmp (Compound r) -> Compound r)
 -> Comp (Path kcmp (Compound r) <: k) r -> Comp k r
fromPath kc = fromField (kc . fromChain)


-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self a = Self deriving (Eq, Show)

instance IsString (Comp k a)
  => IsString (Comp (Self <: k) a) where
  fromString "" = send Self
  fromString s = inj (fromString s)

showSelf :: Comp (Self <: k) ShowS -> Comp k ShowS
showSelf = handle (\ _ _ -> return id)

fromSelf :: IsString r => Comp (Self <: k) r -> Comp k r
fromSelf = handle (\ _ _ -> return (fromString ""))
