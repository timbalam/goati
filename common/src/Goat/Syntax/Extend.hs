{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, ConstraintKinds, TypeOperators, RankNTypes #-}
--{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Goat.Syntax.Extend
  where

import Goat.Co
import Goat.Syntax.Block
  ( Block_(..), Block(..), parseBlock, fromBlock, showBlock )
import Goat.Syntax.Field
  ( Field_(..), Path_, Path(..)
  , parsePath, fromPath, showPath, runPath
  , Chain_, Chain(..)
  )
import Goat.Syntax.Let
 ( Let_(..), Let(..), parseLet, showLet, showLet', fromLet
 --, Pun_, Pun, fromPun, parsePun, showPun
 )
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
  
type BlockStmt_ s =
  ( Let_ s, ExtendBlock_ (Rhs s), Stmt (Rhs s) ~ s
  )
  -- s, Lhs s, Rhs s, Ext (Rhs s)

newtype BlockStmt lhs rhs rext a =
  BlockStmt
    (Let
      lhs
      (rhs (ExtendBlock a rext Null))
      a)

instance Let_ (Comp (BlockStmt lhs rhs rext <: t) a) where
  type Lhs (Comp (BlockStmt lhs rhs rext <: t) a) = lhs
  type Rhs (Comp (BlockStmt lhs rhs rext <: t) a) =
    rhs
      (ExtendBlock
        (Comp (BlockStmt lhs rhs rext <: t) a)
        rext
        Null)
  l #= r = send (BlockStmt (l :#= r))

showBlockStmt
 :: (lhs -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> rhs e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> rext e -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (BlockStmt lhs rhs rext <: t) ShowS -> ShowS
showBlockStmt sl sr srx st =
  st
  . handle (\ (BlockStmt s@(l :#= r)) k ->
      return
        (showLet'
          sl
          (sr (showExtendBlock (st . k) srx runComp))
          (l :#= r)))

fromBlockStmt
 :: BlockStmt_ s 
 => (lhs -> Lhs s)
 -> (forall e . (Comp e (Rhs s) -> Rhs s) -> rhs e -> Rhs s)
 -> (forall e .
      (Comp e (Ext (Rhs s)) -> Ext (Rhs s))
       -> rext e -> Ext (Rhs s))
 -> (Comp t s -> s)
 -> Comp (BlockStmt lhs rhs rext <: t) s -> s
fromBlockStmt kl kr krx kt =
  kt
  . handle (\ (BlockStmt (l :#= r)) k ->
      return
        (kl l #=
          kr (fromExtendBlock (kt . k) krx runComp) r))

type Match_ s = (Path_ s, BlockStmt_ s, Path_ (Lhs s))
  -- s, Lhs s, Compound s, Compound (Lhs s), Rhs s, Ext (Rhs s)
  
parseMatch :: Match_ s => Parser s
parseMatch = do
  p <- parsePath
  (do
    eq <- parseLet
    r <- parsePatt
    return (runPath p `eq` r))
    <|> return (runPath p)
  where
    parsePatt = do
      p <- parsePath <|> parseBlock parseMatch
      ext <- extNext parseMatch
      return (ext p)
    
    extNext ps = go id where
      go k = (do
        f <- parseExtend
        b <- parseBlock ps
        go ((`f` b) . k))
        <|> return k


type Match cmp lhs lcmp rhs rext t =
  Path cmp (BlockStmt (lhs (Path lcmp Null)) rhs rext <: t)

showMatch
 :: (forall e . (Comp e ShowS -> ShowS) -> cmp e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lhs e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lcmp e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> rhs e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> rext e -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Match cmp lhs lcmp rhs rext t) ShowS -> ShowS
showMatch sc sl slc sr srx st =
  showPath
    sc
    (showBlockStmt
      (sl (showPath slc runComp))
      sr
      srx
      st)

fromMatch
 :: Match_ s
 => (forall e
    . (Comp e (Compound s) -> Compound s)
      -> cmp e -> Compound s)
 -> (forall e
    . (Comp e (Lhs s) -> Lhs s) -> lhs e -> Lhs s)
 -> (forall e
    . (Comp e (Compound (Lhs s)) -> Compound (Lhs s))
      -> lcmp e -> Compound (Lhs s))
 -> (forall e
    . (Comp e (Rhs s) -> Rhs s) -> rhs e -> Rhs s)
 -> (forall e
    . (Comp e (Ext (Rhs s)) -> Ext (Rhs s))
      -> rext e -> Ext (Rhs s))
 -> (Comp t s -> s)
 -> Comp (Match cmp lhs lcmp rhs rext t) s -> s
fromMatch kc kl klc kr krx kt =
  fromPath
    kc
    (fromBlockStmt
      (kl (fromPath klc runComp))
      kr
      krx
      kt)


-- | Let pattern statement (define a pattern to be equal to a value)
type LetPatt_ s =
  ( Let_ s, Path_ s, Path_ (Lhs s), ExtendBlock_ (Lhs s) )
  -- s, Compound s, Lhs s, Compound (Lhs s), Rhs s, Stmt (Lhs s), Ext (Lhs s)

-- | Parse a statement of a block expression
parseLetPatt
 :: LetPatt_ s
 => Parser (Stmt (Lhs s))
 -> Parser (Rhs s)
 -> Parser s
parseLetPatt pls pr =
  do
    p <- parsePath
    (do
      ext <- extNext pls
      eq <- parseLet
      rhs <- pr
      return (ext (runPath p) `eq` rhs))
      <|> return (runPath p)
  where
    extNext
     :: (Extend_ s, Block_ (Ext s))
     => Parser (Stmt (Ext s))
     -> Parser (s -> s)
    extNext ps = go id where
      go k = (do
        f <- parseExtend
        b <- parseBlock ps
        go ((`f` b) . k))
        <|> return k

type LetPatt cmp lhs lcmp lstmt lext rhs t =
  Path
    cmp
    (Let
      (lhs
        (Path
          lcmp
          (ExtendBlock
            lstmt
            lext
            Null)))
      rhs
      <: t)

showLetPatt
 :: (forall e . (Comp e ShowS -> ShowS) -> cmp e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lhs e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lcmp e -> ShowS)
 -> (lstmt -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lext e -> ShowS)
 -> (rhs -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (LetPatt cmp lhs lcmp lstmt lext rhs t) ShowS -> ShowS
showLetPatt sc sl slc sls slx sr st =
  showPath
    sc
    (showLet
      (sl
        (showPath
          slc
          (showExtendBlock
            sls
            slx
            runComp)))
      sr
      st)
    

fromLetPatt
 :: LetPatt_ s
 => (forall e
      . (Comp e (Compound s) -> Compound s)
        -> cmp e -> Compound s)
 -> (forall e
      . (Comp e (Lhs s) -> Lhs s) -> lhs e -> Lhs s)
 -> (forall e
      . (Comp e (Compound (Lhs s)) -> Compound (Lhs s))
        -> lcmp e -> Compound (Lhs s))
 -> (lstmt -> Stmt (Lhs s))
 -> (forall e
      . (Comp e (Ext (Lhs s)) -> Ext (Lhs s))
        -> lext e -> Ext (Lhs s))
 -> (rhs -> Rhs s)
 -> (Comp t s -> s)
 -> Comp (LetPatt cmp lhs lcmp lstmt lext rhs t) s -> s
fromLetPatt kc kl klc kls klx kr kt =
  fromPath
    kc
    (fromLet
      (kl 
        (fromPath
          klc
          (fromExtendBlock
            kls
            klx
            runComp)))
      kr
      kt)
