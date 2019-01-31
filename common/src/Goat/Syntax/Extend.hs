{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, DeriveFunctor, ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
--{#--, FunctionalDependencies #-}
module Goat.Syntax.Extend
  where

import Goat.Syntax.Block (Block_(..), Block(..))
import Goat.Co
import Text.Parsec.Text (Parser)

infixl 9 #, :#

-- | Parse a value extension
data Extend x a = a :# x deriving (Eq, Show)

instance Sub (Extend x) (Extend x) where inj = id

type family Ext r
class Extend_ r where
  --type Ext r
  (#) :: r -> Ext r -> r
  
--class Extend__ r ext | r -> ext where
--  (#|) :: r -> ext -> r

instance Extend_ (Free (Co (Extend x)) a) where
  type Ext (Free (Co (Extend x)) a) = x
  a # x = co (a :# x) id
  
instance (Sub f g, Extend_ (Free (Co g) a))
 => Extend_ (Free (Co f) a) where
  type Ext (Free (Co f) a) = Ext (Free (Co g) a)
  a  # x
  
instance (Sub (Extend x) f, Ext (Free (Co f) a) ~ x)
 => Extend_ (Free (Co f) a) where
  --type Ext (Free (Co f) a) = x
  a # x = co (a :# x) id

  
parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

showExtend
 :: (x -> ShowS) -> (a -> ShowS) -> Extend x a -> ShowS
showExtend sx sa (a :# x) = sa a . sx x

fromExtend
 :: Extend_ r => (x -> Ext r) -> (a -> r) -> Extend x a -> r
fromExtend kx ka (a :# x) = ka a # kx x


-- | Create or extend a value with a literal block
type ExtendBlock_ r =
  ( Block_ r, Extend_ r, Block_ (Ext r), Stmt (Ext r) ~ Stmt r )