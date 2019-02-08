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

handleField
  :: (Field cmp x -> a)
  -> Comp (Field cmp <: t) a -> Comp t a
handleField f = handle (\ (c :#. i) _ -> pure (f (c :#. i)))

showField
 :: (cmp -> ShowS)
 -> Comp (Field cmp <: t) ShowS -> Comp t ShowS
showField sc = handleField (showField' sc)
--  handle (\ r _ -> pure (showField' sc r))

showField' :: (cmp -> ShowS) -> Field cmp a -> ShowS
showField' sc (c :#. i) =
  sc c . showChar ' ' . showSymbol "."
    . showChar ' ' . runComp (showIdent (fromString i))

fromField
 :: Field_ r
 => (cmp -> Compound r)
 -> Comp (Field cmp <: t) r -> Comp t r
fromField kc = handleField (fromField' kc)
--  handle (\ r _ -> pure (fromField' kc r))

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
type Path cmp t = 
  Field (cmp (Chain <: Self <: Ident <: Null)) <: t

instance Field_ (Comp (Chain <: t) a) where
  type Compound (Comp (Chain <: t) a) = Comp (Chain <: t) a
  c #. i = send (Chain (c :#. i))

instance IsString (Comp t a) => IsString (Comp (Chain <: t) a)
  where
    fromString s = inj (fromString s)

handleChain
 :: (Chain a -> a)
 -> Comp (Chain <: t) a -> Comp t a
handleChain f = handle (\ (Chain (x :#. i)) k -> do
  a <- k x
  return (f (Chain (a :#. i))))

handlePath
  :: (Field (cmp (Chain <: Self <: Ident <: Null)) <: t)
  -> Comp (Path cmp t) a -> Comp t a

showChain
 :: Comp (Chain <: t) ShowS -> Comp t ShowS
showChain =
  handleChain (\ (Chain f) -> showField' id f)
    
showPath
 :: (forall e . cmp e -> Comp e ShowS)
 -> Comp (Path cmp t) ShowS -> Comp t ShowS
showPath sc =
  showField (runComp . showIdent . showSelf . showChain . sc)   

fromChain
 :: Chain_ r => Comp (Chain <: t) r -> Comp t r
fromChain = handleChain (\ (Chain f) -> fromField' id f)

fromPath
 :: Path_ r
 => (forall e . cmp e -> Comp e (Compound r))
 -> Comp (Path cmp t) r -> Comp t r
fromPath kc =
  fromField (runComp . fromIdent . fromSelf . fromChain . kc)


-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self a = Self deriving (Eq, Show)

instance IsString (Comp t a)
  => IsString (Comp (Self <: t) a) where
  fromString "" = send Self
  fromString s = inj (fromString s)

handleSelf :: a -> Comp (Self <: t) a -> Comp t a
handleSelf a = handle (\ _ _ -> pure a)

showSelf
 :: Comp (Self <: t) ShowS -> Comp t ShowS
showSelf = handleSelf id

fromSelf
 :: IsString r => Comp (Self <: t) r -> Comp t r
fromSelf = handleSelf (fromString "")
