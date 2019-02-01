{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds #-}
--{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Goat.Syntax.Extend
  where

import Goat.Syntax.Block (Block_(..), Block(..))
import Text.Parsec.Text (Parser)

infixl 9 #, :#

-- | Parse a value extension
data Extend x a =
    Path a
  | Extend x a :# x
  deriving (Eq, Show)

class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r

instance Extend_ (Extend x a) where
  type Ext (Extend x a) = x
  (#) = (:#)

instance Block_ a => Block_ (Extend x a) where
  type Stmt (Extend x a) = Stmt a
  block_ = Path . block_
  
parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

showExtend
 :: (x -> ShowS) -> (a -> ShowS) -> Extend x a -> ShowS
showExtend sx sa (Path a) = sa a
showExtend sx sa (m :# x) = showExtend sx sa m . sx x

fromExtend
 :: Extend_ r => (x -> Ext r) -> (a -> r) -> Extend x a -> r
fromExtend kx ka (Path a) = ka a
fromExtend kx ka (m :# x) = fromExtend kx ka m # kx x


-- | Create or extend a value with a literal block
type ExtendBlock_ r =
  ( Block_ r, Extend_ r, Block_ (Ext r), Stmt (Ext r) ~ Stmt r )

type ExtendBlock s x a = Extend (Block s x) (Block s a)