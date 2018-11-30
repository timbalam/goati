{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts #-}

module Goat.Syntax.Field
  where
  
import Goat.Syntax.Ident
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Data.String (IsString(..))

  
infixl 9 #., :#.


-- | A single decimal point / field accessor
data Point = Point

parsePoint :: Parser Point
parsePoint =
  Parsec.try (do
    Parsec.char '.'
    Parsec.notFollowedBy (Parsec.char '.')
    return Point)
    <* spaces
    
showPoint :: ShowS
showPoint = showString "."
  

-- | Reference a component of a compound type
data FieldDT a = a :#. Ident 

class Field r where
  type Compound r
  (#.) :: Compound r -> Ident -> r

instance Field (FieldDT a) where
  type Compound (FieldDT a) = a
  (#.) = (:#.)

parseField :: Field r => Parser (Compound r -> r)
parseField = (do 
  parsePoint 
  i <- parseIdent
  return (#. i))

showField :: (a -> ShowS) -> FieldDT a -> ShowS
showField showa (a :#. i) =
  showa a . showPoint . showIdent i
  
fromField :: Field r => FieldDT (Compound r) -> r
fromField (a :#. i) = a #. i

newtype DFieldDT r =
  DField { runDField :: forall x . (r -> Ident -> x) -> x }

instance Field (DFieldDT r) where
  type Compound (DFieldDT r) = r
  r #. i = DField (\ p -> p r i)
  
fromDField :: Field r => DFieldDT (Compound r) -> r
fromDField (DField f) = f (#.)

instance Eq r => Eq (DFieldDT r) where
  a == b = fromDField a == (fromDField b :: FieldDT r)
  
instance Show r => Show (DFieldDT r) where
  showsPrec n a = showParen (n>10)
    (showString "fromField "
      . showString (fromDField a :: FieldDT r))


-- | Nested field accesses
type Chain r = (Field r, Compound r ~ r)

parseFields_
 :: (Field r, Chain (Compound r))
 => Parser (FieldDT (Compound r) -> r)
parseFields_ =
  (do
    f <- parseField
    fs <- parseFields_
    return (fs . f . fromField))
    <|> return fromField
    
parseFields
 :: (Field r, Chain (Compound r))
 => Parser (Compound r -> Ident -> r)
parseFields =
  (do
    f <- parseFields1
    return (\ a i -> f (a #. i)))
    <|> return (#.)
    
parseFields1
 :: (Field r, Chain (Compound r))
 => Parser (Compound r -> r)
parseFields1 =
  do
    f <- parseField
    fs <- parseFields
    return (\ a -> runDField (f a) fs)

-- | Ident path
type Path r =
  (Field r, IsString (Compound r), Chain (Compound r))

-- | Self reference
data SelfDT = Self

instance IsString SelfDT where
  fromString s = case Parsec.parse (parseSelf <* Parsec.eof) s of
    Left err -> error (show err)
    Right a  -> a
  
parseSelf :: Parser SelfDT
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
 :: (Field a, IsString (Compound a), Chain (Compound a))
 => Parser a
relpath = do
  parseSelf
  f <- parseFields1
  return (f "")

-- | 'localpath' parses a path begining with an identifier
-- e.g. 
--     a
--     a.b
localpath
 :: ( IsString a, Field a
    , IsString (Compound a), Chain (Compound a)
    )
 => Parser a
localpath = do 
  Ident s <- parseIdent
  (do
    f <- parseFields1
    return (f (fromString s)))
    <|> return (fromString s)
