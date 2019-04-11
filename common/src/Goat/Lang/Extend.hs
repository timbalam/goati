{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds, TypeOperators, RankNTypes, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
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

data Extend ext a = a :# ext a
  deriving (Eq, Show, Functor, Foldable, Traversable)

showExtend
 :: (forall x . (x -> ShowS) -> ext x -> ShowS)
 -> (a -> ShowS) -> Extend ext a -> ShowS
showExtend sx sa (a :# x) = sa a . sx sa x

fromExtend
 :: Extend_ r
 => (forall x . (x -> r) -> ext x -> Ext r)
 -> (a -> r) -> Extend ext a -> r
fromExtend kx ka (a :# x) = ka a # kx ka x

instance MemberU Extend r => Extend_ (Union r (Comp r a)) where
  type Ext (Union r (Comp r a)) = UIndex Extend r (Comp r a)
  a # x = injU (join (sendU a) :# x)

showExtendU
 :: Traversable ext
 => (forall x. (x -> ShowS) -> ext x -> ShowS)
 -> (forall x. (x -> ShowS) -> Union t x -> ShowS)
 -> (Comp (Extend ext <: t) a -> ShowS)
 -> Union (Extend ext <: t) (Comp (Extend ext <: t) a) -> ShowS
showExtendU sx st sa = handleU (showExtend sx sa) (st sa)

fromExtendU
 :: (Traversable ext, Extend_ r)
 => (forall x . (x -> r) -> ext x -> Ext r)
 -> (forall x . (x -> r) -> Union t x -> r)
 -> (Comp (Extend ext <: t) a -> r)
 -> Union (Extend ext <: t) (Comp (Extend ext <: t) a) -> r
fromExtendU kx kt ka = handleU (fromExtend kx ka) (kt ka)

instance MemberU Extend r => Extend_ (Comp r a) where
  type Ext (Comp r a) = UIndex Extend r (Comp r a)
  a # x = join (send (a :# x))

showExtendC
 :: Traversable ext
 => (forall x. (x -> ShowS) -> ext x -> ShowS)
 -> Comp (Extend ext <: t) ShowS
 -> Comp t ShowS
showExtendC sx =
  handle (\ a k -> showExtend sx id <$> traverse k a)

fromExtendC
 :: (Traversable ext, Extend_ r)
 => (forall x. (x -> r) -> ext x -> Ext r)
 -> Comp (Extend ext <: t) r
 -> Comp t r
fromExtendC kx =
  handle (\ a k -> fromExtend kx id <$> traverse k a)


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

type ExtendBlock stmt t =
  Extend (Block stmt) <: Block stmt <: Var <: Field <: t

type SomePathExtendBlock stmt = Comp (ExtendBlock stmt Null) Void
{-
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
-}

showPathExtendBlock
 :: (forall x . (x -> ShowS) -> stmt x -> ShowS)
 -> Comp (PathExtendBlock stmt t) ShowS -> Comp t ShowS
showPathExtendBlock ss =
  showField (run . showVarChain)
    . showVar
    . showBlock ss
    . showExtend (run . showBlock ss . getBlock)

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
