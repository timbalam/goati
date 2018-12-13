{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts #-}

module Goat.Syntax.Field
  where
  
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident (Ident(..), parseIdent, showIdent)
import Goat.Syntax.Prec (Op(..), Precedence, doesNotPreceed, parsePoint, showPoint)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import qualified Data.Text as Text
import Data.String (IsString(..))

  
infixl 9 #., :#.

-- | Reference a component of a compound type
data Field a = a :#. Ident
  deriving (Eq, Show)

class Field_ r where
  type Compound r
  (#.) :: Compound r -> Ident -> r

instance Field_ (Field a) where
  type Compound (Field a) = a
  (#.) = (:#.)

parseField :: Field_ r => Parser (Compound r -> r)
parseField = (do 
  parsePoint 
  i <- parseIdent
  return (#. i))

showField
  :: ((Op -> Bool) -> a -> ShowS)
  -> (Op -> Bool) -> Field a -> ShowS
showField showa pred (a :#. i) =
  showParen (pred Point)
    (showa (`doesNotPreceed` Point) a . showPoint . showIdent i)
  
fromField :: Field_ r => Field (Compound r) -> r
fromField (a :#. i) = a #. i

newtype DField r =
  DField { runDField :: forall x . (r -> Ident -> x) -> x }

instance Field_ (DField r) where
  type Compound (DField r) = r
  r #. i = DField (\ p -> p r i)
  
fromDField :: Field_ r => DField (Compound r) -> r
fromDField (DField f) = f (#.)

instance Eq r => Eq (DField r) where
  a == b = fromDField a == specialisedFromDField b
    where
      specialisedFromDField :: DField a -> Field a
      specialisedFromDField = fromDField
  
instance Show r => Show (DField r) where
  showsPrec n a = showParen (n>10)
    (showString "fromField "
      . showsPrec 11 (specialisedFromDField a))
    where
      specialisedFromDField :: DField a -> Field a
      specialisedFromDField = fromDField


-- | Nested field accesses
type Chain_ r = (Field_ r, Compound r ~ r)

parseFields_
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Field (Compound r) -> r)
parseFields_ =
  (do
    f <- parseField
    fs <- parseFields_
    return (fs . f . fromField))
    <|> return fromField
    
parseFields
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> Ident -> r)
parseFields =
  (do
    f <- parseFields1
    return (\ a i -> f (a #. i)))
    <|> return (#.)
    
parseFields1
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> r)
parseFields1 =
  do
    f <- parseField
    fs <- parseFields
    return (\ a -> runDField (f a) fs)

-- | Ident path
type Path_ r =
  (Field_ r, IsString (Compound r), Chain_ (Compound r))

-- | Self reference
data Self = Self

instance IsString Self where
  fromString s = case result of
    Left err -> error (show err)
    Right a  -> a
    where
      result = Parsec.parse
        (parseSelf <* Parsec.eof)
        ""
        (Text.pack s) 
  
parseSelf :: Parser Self
parseSelf = return Self

showSelf :: ShowS
showSelf = id

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
  parseSelf
  f <- parseFields1
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
  Ident s <- parseIdent
  (do
    f <- parseFields1
    return (f (fromString s)))
    <|> return (fromString s)
