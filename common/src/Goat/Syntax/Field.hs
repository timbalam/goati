{-# LANGUAGE RankNTypes, TypeFamilies, ConstraintKinds, FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}
--{-# LANGUAGE StandaloneDeriving, UndecidableInstances #-}
module Goat.Syntax.Field
  where
  
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Ident (Ident(..), parseIdent, showIdent)
import Goat.Syntax.Symbol (Symbol(..), parseSymbol, showSymbol)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import qualified Data.Text as Text
import Data.String (IsString(..))
import Data.Void (Void, absurd)


infixl 9 #., :#.

-- | Reference a component of a compound type
data Field cmp a =
    Term a
  | cmp :#. Ident
  deriving (Eq, Show)

class Field_ r where
  type Compound r
  (#.) :: Compound r -> Ident -> r

instance Field_ (Field cmp a) where
  type Compound (Field cmp a) = cmp
  (#.) = (:#.)
  
instance IsString a => IsString (Field cmp a) where
  fromString s = Compound (fromString s)

parseField :: Field_ r => Parser (Compound r -> r)
parseField = (do 
  parseSymbol "."
  i <- parseIdent
  return (#. i))
  
showField
 :: (cmp -> ShowS) -> (a -> ShowS) -> Field cmp a -> ShowS
showField sc sa (Term a) = sa a
showField sc sa (c :#. i) =
  sc c . showChar ' ' . showSymbol "."
    . showChar ' ' . showIdent i

fromField
 :: Field_ r
 => (cmp -> Compound r) -> (a -> r) -> Field cmp a -> r
fromField kc ka (Term a) = ka a
fromField kc ka (c :#. i) = kc c #. i


-- | Nested field accesses
data Chain a = Chain (Field (Chain a) a) deriving (Eq, Show)

type Chain_ r = (Field_ r, Compound r ~ r)

--deriving instance (Eq (Field (Chain a) a)) => Eq (Chain a)
--deriving instance (Show (Field (Chain a) a)) => Show (Chain a)
instance Field_ (Chain a) where
  type Compound (Chain a) = Chain a
  c #. i = Chain (c :#. i)
  
instance IsString a => IsString (Chain a) where
  fromString s = Chain (Compound (fromString s))
    
parseChain
 :: (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> Ident -> r)
parseChain =
  (do
    f <- parseChain1
    return (\ c i -> f (c #. i)))
    <|> return (#.)
    
parseChain1
 :: forall r 
  . (Field_ r, Chain_ (Compound r))
 => Parser (Compound r -> r)
parseChain1 =
  do
    f <- parseField
    fs <- parseChain
    return (\ c -> case f c of c' :#. i -> fs c' i)
    
fromChain
 :: Chain_ r => (a -> r) -> Chain a -> r
fromChain ka (Chain (Term a)) = ka
fromChain ka (Chain (ch :# i)) = fromChain ka ch # i 

-- | Ident path
type Path cmp a = Field (Chain cmp) a
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
    
fromPath
 :: Path_ r => (cmp -> r) -> (a -> r) -> Path cmp a -> r
fromPath kc ka (Term a) = ka a
fromPath kc ka (ch #: i) = fromChain kc ka # i
