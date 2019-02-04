{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, GeneralizedNewtypeDeriving #-}
--{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module Goat.Syntax.Field
  where
  
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
data Field cmp a =
    NoField a
  | cmp :#. String
  deriving (Eq, Show)

class Field_ r where
  type Compound r
  (#.) :: Compound r -> String -> r

instance Field_ (Field cmp a) where
  type Compound (Field cmp a) = cmp
  (#.) = (:#.)
  
instance IsString a => IsString (Field cmp a) where
  fromString s = NoField (fromString s)
  
showField
 :: (cmp -> ShowS) -> (a -> ShowS) -> Field cmp a -> ShowS
showField sc sa (NoField a) = sa a
showField sc sa (c :#. i) =
  sc c . showChar ' ' . showSymbol "."
    . showChar ' ' . showIdent absurd (fromString i)

parseField :: Field_ r => Parser (Compound r -> r)
parseField = (do 
  parseSymbol "."
  i <- parseIdent
  spaces
  return (#. i))

fromField
 :: Field_ r
 => (cmp -> Compound r) -> (a -> r) -> Field cmp a -> r
fromField kc ka (NoField a) = ka a
fromField kc ka (c :#. i) = kc c #. i


-- | Nested field accesses
newtype Chain a = Chain (Field (Chain a) a)
  -- Chain
  --   { runChain :: forall r . Field_ r => Field r r }
  deriving (Eq, Show, IsString)

type Chain_ r = (Field_ r, Compound r ~ r)

instance Field_ a => Field_ (Chain a) where
  type Compound (Chain a) = Chain a
  c #. i = Chain (fromChain id c :#. i)

instance Field_ (Chain a) where
  type Compound (Chain a) = Chain a
  c #. i = Chain (c :#. i)

showChain :: (a -> ShowS) -> Chain a -> ShowS
showChain sa (Chain f) = showField (showChain sa) sa f

parseChain :: Chain_ r => Parser (r -> r)
parseChain = do
  f <- parseField
  (do
    f' <- parseChain
    return (f . f'))
    <|> return f

fromChain
 :: Chain_ r => (a -> r) -> Chain a -> r
fromChain ka (Chain f) = fromField (fromChain ka) ka f 

{-
parseChain'
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> String -> r)
parseChain =
  (do
    f <- parseChain1
    return (\ c i -> f (c #. i)))
    <|> return (#.)
    
parseChain1'
 :: forall r 
  . (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> r)
parseChain1 =
  do
    f <- parseField
    fs <- parseChain
    return (\ c -> case f c of c' :#. i -> fs c' i)
-}

-- | Ident path
type Path cmp a = Field (Chain (Self (Ident cmp))) a
type Path_ r =
  (Field_ r, IsString (Compound r), Chain_ (Compound r))

showPath
 :: (cmp -> ShowS) -> (a -> ShowS) -> Path cmp a -> ShowS
showPath sc sa =
  showField (showChain (showSelf (showIdent sc))) sa

parsePath
 :: Path_ r => Parser (Compound r -> r)
parsePath = do
  f <- parseField
  c <- parseChain (parseSelf <|> pc)
  return (f c)

fromPath
 :: Path_ r
 => (cmp -> Compound r) -> (a -> r) -> Path cmp a -> r
fromPath kc ka =
  fromField (fromChain (fromSelf (fromIdent kc))) ka


-- | Self reference
data Self a =
    NoSelf a
  | Self
  deriving (Eq, Show)

instance IsString (Self (Ident a)) where
  fromString s = case result of
    Left err -> error (show err)
    Right a  -> a
    where
      result = Parsec.parse
        (parseSelf <* Parsec.eof)
        ""
        (Text.pack s)

showSelf :: (a -> ShowS) -> Self a -> ShowS
showSelf sa (NoSelf a) = sa a
showSelf sa Self = id
        
parseSelf :: Parser (Self (Ident a))
parseSelf =
  (do
    i <- parseIdent
    return (NoSelf (Ident i)))
    <|> return Self

fromSelf :: IsString r => (a -> r) -> Self a -> r
fromSelf ka (NoSelf i) = ka i
fromSelf ka Self = fromString ""

{-
-- | Generic path parsing
--
-- For example
--     x.y.z
-- could be parsed, depending on what follows, as:
-- - a lhs of an assignment;
-- - a pun;
-- - a rhs path.
-- 
-- 'relpath' parses a path beginning with a relative field,
-- e.g. 
--     .y
relpath
 :: (Field_ a, IsString (Compound a), Chain_ (Compound a))
 => Parser a
relpath = do
  f <- parseChain1
  return (f (fromString ""))

-- | 'localpath' parses a path begining with an identifier
-- e.g. 
--     a
--     a.b
localpath
 :: ( IsString a, Field_ a
    , IsString (Compound a), Chain_ (Compound a)
    )
 => Parser a
localpath = do 
  s <- parseIdent
  spaces
  (do
    f <- parseChain1
    return (f (fromString s)))
    <|> return (fromString s)
-}