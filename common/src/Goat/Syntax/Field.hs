{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances #-}

module Goat.Syntax.Field
  where
  
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident (Ident(..), parseIdent, showIdent)
import Goat.Syntax.Symbol (Symbol(..), parseSymbol, showSymbol)
import Goat.Syntax.Binop (Precedence, doesNotPreceed)
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
  parseSymbol Point 
  i <- parseIdent
  return (#. i))
  
showField :: (a -> ShowS) -> Field a -> ShowS
showField showa (a :#. i) = showa a . showSymbol Point . showIdent i
  
fromField :: Field_ r => (a -> Compound r) -> Field a -> r
fromField froma (a :#. i) = froma a #. i

fromField' :: Field_ r => Field (Compound r) -> r
fromField' = fromField id


-- | Nested field accesses
type Chain_ r = (Field_ r, Compound r ~ r)
    
parseChain
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Field (Compound r) -> r)
parseChain =
  (do
    f <- parseChain1
    return (f . fromField'))
    <|> return (#.)
    
parseChain1
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> r)
parseChain1 =
  do
    f <- parseField
    fs <- parseChain
    return (fs . f)

-- | Ident path
type Path_ r =
  (Field_ r, IsString (Compound r), Chain_ (Compound r))


-- | Self reference
data Self = Self

instance IsString Self where
  fromString s = case result of
    Left err -> error (show err)
    Right _  -> Self
    where
      result = Parsec.parse
        Parsec.eof
        ""
        (Text.pack s)

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
  Ident s <- parseIdent
  (do
    f <- parseChain1
    return (f (fromString s)))
    <|> return (fromString s)
