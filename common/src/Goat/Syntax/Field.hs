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

instance DSend m => Field_ ((m <<: Field cmp) t) where
  type Compound ((m <<: Field cmp) t) = cmp
  c #. i = dsend (c :#. i)

instance IsString (m (Field cmp <: t))
 => IsString ((m <<: Field cmp) t) where
  fromString s = EComp (fromString s)

showField
 :: (DIter m, DView m, DVal m ~ ShowS)
 => (cmp -> ShowS)
 -> (m <<: Field cmp) t -> m t
showField pure sc =
  dhandle (\ r _ -> dpure (showField' sc r))

showField' :: (cmp -> ShowS) -> Field cmp a -> ShowS
showField' sc (c :#. i) =
  sc c . showChar ' ' . showSymbol "."
    . showChar ' ' . runDComp (showIdent (fromString i))

fromField
 :: (DIter m, DView m, Field_ (DVal m))
 => (cmp -> Compound (DVal m))
 -> (m <<: Field cmp) t -> m t
fromField kc =
  dhandle (\ r _ -> dpure (fromField' kc r))

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
 => (DComp Void <<: Field (Compound r)) Null-> r
runPath m =
  runDComp (fromField absurd id m)

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
  Field ((cmp <<: Chain <<: Ident <<: Self) Null)

instance DSend m => Field_ ((m <<: Chain) t) where
  type Compound ((m <<: Chain) t) = (m <<: Chain) t
  c #. i = send (Chain (c :#. i))

handleChain
 :: (DIter m, DView m)
 => (Chain (DVal m) -> DVal m)
 -> (m <<: Chain) t -> m t
handleChain f = handle (\ (Chain (c :#. i)) k ->
  dbind (k c) (\ a -> dpure (f (Chain (a :#. i)))))

showChain
 :: (DIter m, DView m, DVal m ~ ShowS)
 => (m <<: Chain) t -> m t
showChain =
  handleChain (\ Chain (s :#. i) -> showField' id (s :#. i))
    
showPath
 :: ( DIter m, DView m, DVal m ~ ShowS
    , DIter cmp, DView cmp, DVal cmp ~ ShowS
    )
 => (cmp Null -> ShowS)
 -> (m <<: Path cmp) t -> m t
showPath sc = showField (sc . showChain . showSelf . showIdent)   

fromChain
 :: (DIter m, DView m, Chain_ (DVal m))
 => (m <<: Chain) t -> m t
fromChain = handleChain (\ (Chain a) -> fromField' id a)

fromPath
 :: (DIter m, DView m, Path_ (DVal m))
 => (cmp Null -> Compound (DVal m))
 -> (m <<: Path cmp) t -> m t
fromPath kc =
  fromField (kc . fromIdent . fromSelf . fromChain)


-- | Self reference
parseSelf :: IsString r => Parser r
parseSelf = return (fromString "")

data Self a = Self deriving (Eq, Show)

instance IsString (m (Self <: t))
  => IsString ((m <<: Self) t) where
  fromString "" = send Self
  fromString s = EComp (fromString s)

handleSelf
 :: (DIter m, DView m)
 => DVal m -> (m <<: Self) t -> m t
handleSelf a = dhandle (\ _ _ -> dpure a)

showSelf
 :: (DIter m, DView m, DVal m ~ ShowS)
 => (m <<: Self) t -> m t
showSelf = handleSelf id

fromSelf
 :: (DIter m, DView m, IsString (DVal m))
 => (m <<: Self) t -> m t
fromSelf = handleSelf (fromString "")
