{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, FlexibleInstances, RankNTypes #-}
module Goat.Syntax.Let
  where
  
import Goat.Co
import Goat.Syntax.Symbol
import Goat.Syntax.Field
  ( Field_(..), Field, fromField
  , Path_, Path, parsePath, fromPath, showPath, runPath
  , Chain_
  )
import Goat.Syntax.Extend
  ( Extend_(..), parseExtend
  , Block_(..), parseBlock
  , ExtendBlock_, ExtendBlock, fromExtendBlock, showExtendBlock
  )
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
import Data.String (IsString(..))
import Data.Void (Void, absurd)
  
infix 1 #=, :#=

-- | Assignment
class Let_ s where
  type Lhs s
  type Rhs s
  (#=) :: Lhs s -> Rhs s -> s

parseLet :: Let_ s => Parser (Lhs s -> Rhs s -> s)
parseLet = parseSymbol "=" >> return (#=)

data Let lhs rhs a = lhs :#= rhs deriving (Eq, Show)

instance Let_ (Comp (Let lhs rhs <: t) a) where
  type Lhs (Comp (Let lhs rhs <: t) a) = lhs
  type Rhs (Comp (Let lhs rhs <: t) a) = rhs
  
  l #= r = send (l :#= r)
  
instance Field_ (Comp t a)
 => Field_ (Comp (Let lhs rhs <: t) a) where
  type Compound (Comp (Let lhs rhs <: t) a) =
    Compound (Comp t a)
  a #. i = inj (a #. i)

instance IsString (Comp t a)
 => IsString (Comp (Let lhs rhs <: t) a) where
  fromString s = inj (fromString s)

showLet
 :: (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Let lhs rhs <: t) ShowS -> ShowS
showLet sl sr st =
  st 
  . handle (\ a _ -> return (showLet' sl sr a))

showLet'
 :: (lhs -> ShowS) -> (rhs -> ShowS) -> Let lhs rhs a -> ShowS
showLet' sl sr (l :#= r) =
  sl l . showChar ' ' . showSymbol "=" . showChar ' ' . sr r

fromLet
 :: Let_ s
 => (lhs -> Lhs s)
 -> (rhs -> Rhs s)
 -> (Comp t s -> s)
 -> Comp (Let lhs rhs <: t) s -> s
fromLet kl kr kt =
  kt
  . handle (\ (l :#= r) _ -> return (kl l #= kr r))

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

type Match_ s =
  ( Path_ s, BlockStmt_ s, Path_ (Lhs s), Path_ (Rhs s) )
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
type Rec_ s =
  ( Let_ s, Path_ s, Path_ (Lhs s), ExtendBlock_ (Lhs s) )
  -- s, Compound s, Lhs s, Compound (Lhs s), Rhs s, Stmt (Lhs s), Ext (Lhs s)

-- | Parse a statement of a block expression
parseRec
 :: Rec_ s
 => Parser (Stmt (Lhs s))
 -> Parser (Rhs s)
 -> Parser s
parseRec pls pr =
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

type Rec cmp lhs lcmp lstmt lext rhs t =
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

showRec
 :: (forall e . (Comp e ShowS -> ShowS) -> cmp e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lhs e -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lcmp e -> ShowS)
 -> (lstmt -> ShowS)
 -> (forall e . (Comp e ShowS -> ShowS) -> lext e -> ShowS)
 -> (rhs -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Rec cmp lhs lcmp lstmt lext rhs t) ShowS -> ShowS
showRec sc sl slc sls slx sr st =
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
    

fromRec
 :: Rec_ s
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
 -> Comp (Rec cmp lhs lcmp lstmt lext rhs t) s -> s
fromRec kc kl klc kls klx kr kt =
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