{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds, TypeOperators, RankNTypes #-}
--{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Goat.Syntax.Extend
  ( module Goat.Syntax.Extend
  , Block_(..), Block, parseBlock, fromBlock, showBlock
  )
  where

import Goat.Co
import Goat.Syntax.Block
  ( Block_(..), Block, parseBlock, fromBlock, showBlock )
import Goat.Syntax.Field (Field_(..))
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Data.String (IsString(..))

infixl 9 #, :#

-- | Parse a value extension
class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r

parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

data Extend ext a = a :# ext deriving (Eq, Show)

instance Extend_ (Comp (Extend ext <: t) a) where
  type Ext (Comp (Extend ext <: t) a) = ext
  a # x = send (a :# x)

instance Block_ (Comp t a)
 => Block_ (Comp (Extend ext <: t) a) where
  type Stmt (Comp (Extend ext <: t) a) = Stmt (Comp t a)
  block_ sbdy = inj (block_ sbdy)

instance Field_ (Comp t a)
 => Field_ (Comp (Extend ext <: t) a) where
  type Compound (Comp (Extend ext <: t) a) = Compound (Comp t a)
  c #. i = inj (c #. i)

showExtend
 :: (ext -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Extend ext <: t) ShowS -> ShowS
showExtend sx st = st . handle (\ (ex :# x) k -> do
  ex <- k ex
  return (ex . sx x))

fromExtend
 :: Extend_ r
 => (x -> Ext r)
 -> (Comp t r -> r)
 -> Comp (Extend x <: t) r -> r
fromExtend kx kt = kt . handle (\ (ex :# x) k -> do
  ex <- k ex
  return (ex # kx x))


-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
-- * Let path pattern (leaf pattern assigns matched value to path)
-- * Block pattern (matches a set of paths to nested (lifted) patterns)
-- * An block pattern with left over pattern (matches set of fields not
--   matched by the block pattern)
type ExtendBlock_ r =
  ( Block_ r, Extend_ r, Block_ (Ext r)
  , Stmt r ~ Stmt (Ext r)
  )
  -- r, Compound r, Stmt r, Ext r

type ExtendBlock stmt ext t =
  Block stmt <: Extend (ext (Block stmt <: Null)) <: t

showExtendBlock
 :: (stmt -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> ext e -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (ExtendBlock stmt ext t) ShowS -> ShowS
showExtendBlock ss se st =
  showBlock
    ss
    (showExtend
      (se (showBlock ss runComp))
      st)

fromExtendBlock
 :: ExtendBlock_ r
 => (stmt -> Stmt r)
 -> (forall e . (Comp e (Ext r) -> Ext r) -> ext e -> Ext r)
 -> (Comp t r -> r)
 -> Comp (ExtendBlock stmt ext t) r -> r
fromExtendBlock ks ke kt =
  fromBlock
    ks
    (fromExtend
      (ke (fromBlock ks runComp))
      kt)
