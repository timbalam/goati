{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, GeneralizedNewtypeDeriving, TypeOperators #-}
--{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module Goat.Syntax.Field
  where

import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident
  ( Ident(..), parseIdent, fromIdent, showIdent )
import Goat.Syntax.Symbol (parseSymbol, showSymbol)
import Goat.Co
  ( Comp(..), (<:)(..), (<<:)(..), Null
  , runComp, inj, send, handle
  )
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
  
instance Field_ (m t a) => Field_ ((m <<: h) t a) where
  type Compound ((m <<: h) t a) = Compound (m t a)
  c #. i = WithEff (inj (c #. i))

showField
 :: (cmp -> ShowS)
 -> Comp (Field cmp <: k) ShowS -> Comp k ShowS
showField sc = handle (\ r _ -> return (showField' sc r))

showField' :: (cmp -> ShowS) -> Field cmp a -> ShowS
showField' sc (c :#. i) =
  sc c . showChar ' ' . showSymbol "."
    . showChar ' ' . runComp (showIdent (fromString i))

fromField
 :: Field_ r
 => (cmp -> Compound r)
 -> Comp (Field cmp <: k) r -> Comp k r
fromField kc = handle (\ r _ -> return (fromField' kc r))

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
  runComp (fromField id (fmap absurd m))

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
type Path cmp = 
  Field (Comp (Chain <: Self <: Ident <: Null) cmp)

instance Field_ (Comp (Chain <: t) a) where
  type Compound (Comp (Chain <: t) a) = Comp (Chain <: t) a
  c #. i = send (Chain (c :#. i))

handleChain
 :: (Chain a -> a) -> Comp (Chain <: t) a -> Comp t a
handleChain f = handle (\ (Chain (c :#. i)) k -> do
  a <- k c
  return (f (Chain (a :#. i))))

showChain :: Comp (Chain <: t) ShowS -> Comp t ShowS
showChain = handleChain (\ (Chain a) -> showField' id a)

showPath
 :: Comp (Path ShowS <: t) ShowS -> Comp t ShowS
showPath = showField (runComp . showIdent . showSelf . showChain)

fromChain :: Chain_ r => Comp (Chain <: t) r -> Comp t r
fromChain = handleChain (\ (Chain a) -> fromField' id a)

fromPath
 :: Path_ r
 => Comp (Path (Compound r) <: t) r -> Comp t r
fromPath = fromField (runComp . fromIdent . fromSelf . fromChain)


-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self a = Self deriving (Eq, Show)

instance IsString (Comp t a)
  => IsString (Comp (Self <: t) a) where
  fromString "" = send Self
  fromString s = inj (fromString s)

handleSelf :: a -> Comp (Self <: t) a -> Comp t a
handleSelf a = handle (\ _ _ -> return a)

showSelf :: Comp (Self <: t) ShowS -> Comp t ShowS
showSelf = handleSelf id

fromSelf :: IsString r => Comp (Self <: t) r -> Comp t r
fromSelf = handleSelf (fromString "")
