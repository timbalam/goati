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

showField
 :: (cmp -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Field cmp <: t) ShowS -> ShowS
showField sc st =
  st 
  . handle (\ (c :#. i) _ ->
      return (showField' sc (c :#. i)))

showField' :: (cmp -> ShowS) -> Field cmp a -> ShowS
showField' sc (c :#. i) =
  sc c . showChar ' ' . showSymbol "."
    . showChar ' ' . showIdent runComp (fromString i)

fromField
 :: Field_ r
 => (cmp -> Compound r)
 -> (Comp t r -> r)
 -> Comp (Field cmp <: t) r -> r
fromField kc kt =
  kt
  . handle (\ (c :#. i) _ ->
      return (fromField' kc (c :#. i)))

fromField'
 :: Field_ r => (cmp -> Compound r) -> Field cmp a -> r
fromField' kc (c :#. i) = kc c #. i


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
    go s)
    <|> go (fromString "")
  where
    go
      :: (Field_ r, Chain_ (Compound r))
      => Compound r -> Parser r
    go c = do
      f <- parseField
      (go (runPath (f c))
        <|> return (runPath (f c)))

runPath
 :: (Field_ r, Chain_ (Compound r))
 => Comp (Field (Compound r) <: Null) Void -> r
runPath m =
  fromField id runComp (fmap absurd m)

runPath'
 :: (Field_ r, Chain_ (Compound r))
 => Comp (Path (Flip Comp (Compound r)) <: Null) 

-- newtype (m <<: h) t a = ExtDom (m (h <: t) a)
-- (<<:)
--   :: ((* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> *  
-- Field cmp a = cmp :#. String
-- Cfield ccmp = Comp <<: Field (ccmp Null)
-- Chain a = Chain (Field a a)
-- Cchain = Comp <<: Chain
-- Path cmpt cmp a =
--   Field (Comp (Chain <: Self <: Ident <: cmpt) cmp) a
-- Cpath ccmp = Cfield (ccmp <<: Chain <<: Self <<: Ident)

newtype Chain a = Chain (Field a a) deriving (Eq, Show)
type Path cmp t = 
  Field (cmp (Chain <: Self <: Ident <: Null)) <: t

instance Field_ (Comp (Chain <: t) a) where
  type Compound (Comp (Chain <: t) a) = Comp (Chain <: t) a
  c #. i = send (Chain (c :#. i))

instance IsString (Comp t a) => IsString (Comp (Chain <: t) a)
  where
    fromString s = inj (fromString s)

showChain
 :: (Comp t ShowS -> ShowS)
 -> Comp (Chain <: t) ShowS -> ShowS
showChain st =
  st
  . handle (\ (Chain (a :#. i)) k -> do
      a <- k a
      return (showField' id (a :#. i)))

showPath
 :: (forall e . (Comp e ShowS -> ShowS) -> cmp e -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Path cmp t) ShowS -> ShowS
showPath sc st =
  showField
    (sc (showChain (showSelf (showIdent runComp))))
    st

fromChain
 :: Chain_ r
 => (Comp t r -> r) 
 -> Comp (Chain <: t) r -> r
fromChain kt =
  kt
  . handle (\ (Chain (a :#. i)) k -> do
      a <- k a
      return (fromField' id (a :#. i)))

fromPath
 :: Path_ r
 => (forall e 
      . (Comp e (Compound r) -> Compound r)
        -> cmp e -> Compound r)
 -> (Comp t r -> r)
 -> Comp (Path cmp t) r -> r
fromPath kc kt =
  fromField
    (kc (fromChain (fromSelf (fromIdent runComp))))
    kt


-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self a = Self deriving (Eq, Show)

instance IsString (Comp t a)
  => IsString (Comp (Self <: t) a) where
  fromString "" = send Self
  fromString s = inj (fromString s)

showSelf
 :: (Comp t ShowS -> ShowS)
 -> Comp (Self <: t) ShowS -> ShowS
showSelf st = st . handle (\ _ _ -> return id)

fromSelf
 :: IsString r
 => (Comp t r -> r)
 -> Comp (Self <: t) r -> r
fromSelf kt = kt . handle (\ _ _ -> return (fromString ""))
