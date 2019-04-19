{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeFamilies, ConstraintKinds #-}
module Goat.Lang.Field
  where

import Goat.Comp
import Goat.Lang.Ident
import Goat.Lang.Comment (spaces)
import Goat.Lang.Symbol
import Goat.Util ((<&>))
import Data.Functor.Identity (Identity(..))
import Data.Void (Void)
--import Control.Monad (join)
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))

infixl 9 #., :#.

-- | Reference a component of a compound type
class Field_ r where
  type Compound r
  (#.) :: Compound r -> Ident -> r

parseField
 :: Field_ r
 => Parser (Compound r -> r)
parseField = do 
  parseSymbol "."
  i <- parseIdent
  spaces
  return (#. i)

data Field cmp a = cmp :#. Ident deriving (Eq, Show)

showField
 :: Functor m => (cmp -> m ShowS) -> Field cmp a -> m ShowS
showField sa (a :#. i) =
  sa a <&> \ a -> 
    a .
      showChar ' ' .
      showSymbol "." .
      showChar ' ' . 
      ident showString i

fromField
 :: (Functor m, Field_ r)
 => (cmp -> m (Compound r))
 -> Field cmp a -> m r
fromField k (a :#. i) = k a <&> \ a -> a #. i

instance Field_ (Field cmp a) where
  type Compound (Field cmp a) = cmp
  a #. i = a :#. i

instance MemberU Field r => Field_ (Comp r a) where
  type Compound (Comp r a) = UIndex Field r
  c #. i = send (c :#. i)


-- | Nested field accesses
type FieldChain_ r = (Field_ r, Compound r ~ r)
  
parseFieldLink
 :: (Field_ r, FieldChain_ (Compound r))
 => Parser (Compound r -> r)
parseFieldLink = do
  f <- parseField
  (do
    g <- parseFieldLink
    return (g . cloneField . f)) <|>
    return (cloneField . f)

cloneField :: Field_ r => Field (Compound r) Void -> r
cloneField = runIdentity . fromField pure
