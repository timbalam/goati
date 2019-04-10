{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds, TypeOperators, RankNTypes #-}
--{-# LANGUAGE UndecidableInstances #-}
--{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Goat.Lang.Extend
  ( module Goat.Lang.Extend
  , module Goat.Lang.Block
  )
  where

import Goat.Comp
import Goat.Lang.Block
import Goat.Lang.Field
import Goat.Lang.Ident
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

instance MemberU Extend r => Extend_ (Comp r a) where
  type Ext (Comp r a) = UIndex Extend r
  a # x = join (send (a :# x))

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
          <: Var
          <: Field SomeVarChain
          <: t)
         a
    }

instance Field_ (SomePathExtendBlock stmt) where
  type Compound (SomePathExtendBlock stmt) = SomeVarChain
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
  showField (run . showVarChain)
    . showVar
    . showBlock ss
    . showExtend (run . showBlock ss . getBlock)
    . getPathExtendBlock

fromPathExtendBlock
 :: (ExtendBlock_ r, Path_ r)
 => (stmt -> Stmt r) 
 -> SomePathExtendBlock stmt -> Comp t r
fromPathExtendBlock ks =
  fromField (run . fromVarChain)
    . fromVar
    . fromBlock ks
    . fromExtend (run . fromBlock ks . getBlock)
    . getPathExtendBlock

pathExtendBlockProof
 :: SomePathExtendBlock stmt -> SomePathExtendBlock stmt
pathExtendBlockProof = run . fromPathExtendBlock id
