{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeFamilies, ConstraintKinds #-}
module Goat.Lang.Field
  where

import Goat.Comp
import Goat.Lang.Ident
import Goat.Lang.Comment (spaces)
import Goat.Lang.Symbol
import Goat.Util ((<&>))
import Control.Monad (join)
import Text.Parsec.Text (Parser)

infixl 9 #., :#.

-- | Reference a component of a compound type
class Field_ r where
  type Compound r
  (#.) :: Compound r -> Ident -> r
  
type Chain_ r = (Field_ r, Compound r ~ r)

parseField
 :: Field_ r
 => Parser (Compound r -> r)
parseField = do 
  parseSymbol "."
  i <- parseIdent
  spaces
  return (#. i)

data Field a = a :#. Ident
  deriving (Eq, Show)

showField
 :: Functor m => Field a -> (a -> m ShowS) -> m ShowS
showField (a :#. i) sa =
  sa a <&> \ a -> 
    a .
      showChar ' ' .
      showSymbol "." .
      showChar ' ' . 
      ident showString i

fromField
 :: (Functor m, Field_ r) => Field a -> (a -> m (Compound r)) -> m r
fromField (a :#. i) k = k a <&> \ a -> a #. i

instance Field_ (Field a) where
  type Compound (Field a) = a
  a #. i = a :#. i

instance Member Field Field where uprism = id

instance Member Field r => Field_ (Comp r a) where
  type Compound (Comp r a) = Comp r a
  c #. i = join (send (c :#. i))
