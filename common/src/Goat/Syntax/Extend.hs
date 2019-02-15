{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds, TypeOperators, RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Goat.Syntax.Extend
  ( module Goat.Syntax.Extend
  , Block_(..), Block, parseBlock, fromBlock, showBlock
  )
  where

import Goat.Co
import Goat.Syntax.Block
  ( Block_(..), Block, parseBlock, fromBlock, showBlock
  , SomeBlock(..) )
import Goat.Syntax.Field
  ( Field_(..), Field, fromField, showField
  , Path_
  , SomeStringChain, showStringChain, fromStringChain 
  , Self
  )
import Goat.Syntax.Ident
  ( Ident(..), fromIdent, showIdent )
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Control.Monad (join)
import Data.String (IsString(..))
import Data.Void

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

instance
  Block_ (Comp t a) => Block_ (Comp (Extend ext <: t) a)
  where
    type Stmt (Comp (Extend ext <: t) a) = Stmt (Comp t a)
    block_ sbdy = inj (block_ sbdy)

instance
  Field_ (Comp t a) => Field_ (Comp (Extend ext <: t) a)
  where
    type Compound (Comp (Extend ext <: t) a) =
      Compound (Comp t a)
    c #. i = inj (c #. i)

instance
  IsString (Comp t a) => IsString (Comp (Extend ext <: t) a)
  where
    fromString s = inj (fromString s)

instance
  Extend_ (Comp t (Comp (Block stmt <: t) a))
   => Extend_ (Comp (Block stmt <: t) a)
  where
    type Ext (Comp (Block stmt <: t) a) =
      Ext (Comp t (Comp (Block stmt <: t) a))
    ex # x = join (inj (return ex # x))

instance
  Extend_ (Comp t (Comp (Field cmp <: t) a))
   => Extend_ (Comp (Field cmp <: t) a)
  where
    type Ext (Comp (Field cmp <: t) a) =
      Ext (Comp t (Comp (Field cmp <: t) a))
    ex # x = join (inj (return ex # x))

instance
  Extend_ (Comp t (Comp (Ident <: t) a))
   => Extend_ (Comp (Ident <: t) a)
  where
    type Ext (Comp (Ident <: t) a) =
      Ext (Comp t (Comp (Ident <: t) a))
    ex # x = join (inj (return ex # x))

instance
  Extend_ (Comp t (Comp (Self <: t) a))
   => Extend_ (Comp (Self <: t) a)
  where
    type Ext (Comp (Self <: t) a) =
      Ext (Comp t (Comp (Self <: t) a))
    ex # x = join (inj (return ex # x))

showExtend
 :: (ext -> ShowS)
 -> Comp (Extend ext <: t) ShowS -> Comp t ShowS
showExtend sx = handle (\ (ex :# x) k -> do
  ex <- k ex
  return (ex . sx x))

fromExtend
 :: Extend_ r
 => (x -> Ext r)
 -> Comp (Extend x <: t) r -> Comp t r
fromExtend kx = handle (\ (ex :# x) k -> do
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
 
newtype SomePathExtendBlock stmt =
  SomePathExtendBlock {
    getPathExtendBlock
     :: forall t a
      . Comp
         (Extend (SomeBlock stmt)
          <: Block stmt
          <: Ident
          <: Field SomeStringChain
          <: t)
         a
    }

instance Field_ (SomePathExtendBlock stmt) where
  type Compound (SomePathExtendBlock stmt) = SomeStringChain
  c #. i = SomePathExtendBlock (c #. i)

instance IsString (SomePathExtendBlock stmt) where
  fromString s = SomePathExtendBlock (fromString s)

instance Block_ (SomePathExtendBlock stmt) where
  type Stmt (SomePathExtendBlock stmt) = stmt
  block_ s = SomePathExtendBlock (block_ s)

instance Extend_ (SomePathExtendBlock stmt) where
  type Ext (SomePathExtendBlock stmt) = SomeBlock stmt
  SomePathExtendBlock ex # x = SomePathExtendBlock (ex # x)

showPathExtendBlock
 :: (stmt -> ShowS)
 -> SomePathExtendBlock stmt -> Comp t ShowS
showPathExtendBlock ss =
  showField (run . showStringChain)
    . showIdent
    . showBlock ss
    . showExtend (run . showBlock ss . getBlock)
    . getPathExtendBlock

fromPathExtendBlock
 :: (ExtendBlock_ r, Path_ r)
 => (stmt -> Stmt r) 
 -> SomePathExtendBlock stmt -> Comp t r
fromPathExtendBlock ks =
  fromField (run . fromStringChain)
    . fromIdent
    . fromBlock ks
    . fromExtend (run . fromBlock ks . getBlock)
    . getPathExtendBlock

pathExtendBlockProof
 :: SomePathExtendBlock stmt -> SomePathExtendBlock stmt
pathExtendBlockProof = run . fromPathExtendBlock id
