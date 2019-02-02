{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds #-}
--{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Goat.Syntax.Extend
  where

import Goat.Syntax.Block
  ( Block_(..), Block(..), fromBlock, showBlock )
import Goat.Syntax.Field
  ( Field_(..), Path_, Path(..), fromPath, showPath
  , Chain_, Chain(..)
  )
import Goat.Syntax.Let
 ( Let_(..), Pun_, Pun(..), fromPun, showPun )
import Text.Parsec.Text (Parser)
import Data.String (IsString(..))

infixl 9 #, :#

-- | Parse a value extension
data Extend ext a =
    NoExtend a
  | Extend ext a :# ext
  deriving (Eq, Show)

class Extend_ r where
  type Ext r
  (#) :: r -> Ext r -> r

instance Extend_ (Extend ext a) where
  type Ext (Extend ext a) = ext
  (#) = (:#)

instance Block_ a => Block_ (Extend ext a) where
  type Stmt (Extend ext a) = Stmt a
  block_ = NoExtend . block_
  
instance Field_ a => Field_ (Extend ext a) where
  type Compound (Extend ext a) = Compound a
  c #. i = NoExtend (c #. i)

parseExtend :: Extend_ r => Parser (r -> Ext r -> r)
parseExtend = pure (#)

showExtend
 :: (ext -> ShowS) -> (a -> ShowS) -> Extend ext a -> ShowS
showExtend sx sa (NoExtend a) = sa a
showExtend sx sa (ex :# x) = showExtend sx sa ex . sx x

fromExtend
 :: Extend_ r => (x -> Ext r) -> (a -> r) -> Extend x a -> r
fromExtend kx ka (NoExtend a) = ka a
fromExtend kx ka (ex :# x) = fromExtend kx ka ex # kx x


-- | Create or extend a value with a literal block
type ExtendBlock stmt ext a =
  Extend (Block stmt ext) (Block stmt a)

type ExtendBlock_ r =
  ( Block_ r, Extend_ r, Block_ (Ext r), Stmt (Ext r) ~ Stmt r )
  -- r, Stmt r, Ext r, Stmt (Ext r)

showExtendBlock
 :: (stmt -> ShowS)
 -> (ext -> ShowS)
 -> (a -> ShowS)
 -> ExtendBlock stmt ext a -> ShowS
showExtendBlock ss sx sa =
  showExtend (showBlock ss sx) (showBlock ss sa)
  
fromExtendBlock
 :: ExtendBlock_ r
 => (stmt -> Stmt r)
 -> (ext -> Ext r)
 -> (a -> r)
 -> ExtendBlock stmt ext a -> r
fromExtendBlock ks kx ka =
  fromExtend (fromBlock ks kx) (fromBlock ks ka)
  
-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
-- * Let path pattern (leaf pattern assigns matched value to path)
-- * Block pattern (matches a set of paths to nested (lifted) patterns)
-- * An block pattern with left over pattern (matches set of fields not
--   matched by the block pattern)
newtype Patt lcmp lhs scmp stmt ext cmp a =
  Patt
    (ExtendBlock
      (Pun
        lcmp
        lhs
        (Patt lcmp lhs scmp stmt ext cmp a)
        scmp
        stmt)
      ext
      (Path cmp a))

showPatt
 :: (lcmp -> ShowS)
 -> (lhs -> ShowS)
 -> (scmp -> ShowS)
 -> (stmt -> ShowS)
 -> (ext -> ShowS)
 -> (cmp -> ShowS)
 -> (a -> ShowS)
 -> Patt lcmp lhs scmp stmt ext cmp a -> ShowS
showPatt slc sl ssc ss sx sc sa (Patt eb) =
  showExtendBlock
    (showPun slc sl (showPatt slc sl ssc ss sx sc sa) ssc ss)
    sx
    (showPath sc sa)
    eb

fromPatt
 :: Patt_ p
 => (lcmp -> Compound (Lhs (Stmt p)))
 -> (lhs -> Lhs (Stmt p))
 -> (scmp -> Compound (Stmt p))
 -> (stmt -> Stmt p)
 -> (ext -> Ext p)
 -> (cmp -> Compound p)
 -> (a -> p)
 -> Patt lcmp lhs scmp stmt ext cmp a -> p
fromPatt slc sl ssc ss sx sc sa (Patt eb) =
  fromExtendBlock
    (fromPun
      slc
      sl
      (fromPatt slc sl ssc ss sx sc sa)
      ssc
      ss)
    sx
    (fromPath sc sa)
    eb

type Patt_ p =
  ( Path_ p, ExtendBlock_ p, Pun_ (Stmt p), Rhs (Stmt p) ~ p )
  -- p, Compound p, Stmt p, Ext p, Lhs (Stmt p), Rhs (Stmt p), Compound (Lhs (Stmt p))
  
instance Field_ (Patt lcmp lhs scmp stmt ext cmp a) where
  type Compound (Patt lcmp lhs scmp stmt ext cmp a) =
    Compound (Path cmp a)
  c #. i = Patt (c #. i)

instance Extend_ (Patt lcmp lhs scmp stmt ext cmp a) where
  type Ext (Patt lcmp lhs scmp stmt ext cmp a) =
    Block
      (Pun
        lcmp
        lhs
        (Patt lcmp lhs scmp stmt ext cmp a)
        scmp
        stmt)
      ext
  Patt ex # x = Patt (ex # x)
  
instance Block_ (Patt lcmp lhs scmp stmt ext cmp a) where
  type Stmt (Patt lcmp lhs scmp stmt ext cmp a) =
    Pun lcmp lhs (Patt lcmp lhs scmp stmt ext cmp a) scmp stmt
  block_ = Patt . block_

  

