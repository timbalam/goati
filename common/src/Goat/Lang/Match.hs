{-# LANGUAGE TypeOperators, ConstraintKinds, FlexibleContexts, TypeFamilies #-}
module Goat.Lang.Match
  where

import Goat.Comp
import Goat.Lang.Ident
import Goat.Lang.Field
import Goat.Lang.Extend
import Goat.Lang.Block
import Goat.Lang.Let
import Goat.Lang.Field
import Goat.Lang.Reflect
import Goat.Lang.Path
import Goat.Lang.Expr
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
import Data.String (IsString(..))
import Data.Void (Void, absurd)

-- | Nested field accesses
type Path_ r =
  ( IsString r, Field_ r
  , IsString (Compound r), Chain_ (Compound r)
  )

parsePath
 :: Path_ r => Parser r
parsePath = 
  (do
    s <- parseIdent
    (do 
      f <- parseChain
      return (f (fromString s))) <|>
        return (fromString s)) <|>
    (do 
      f <- parseChain
      return (f (fromString "")))

type VarField c t = Field c <: Var <: t

fromVarFieldM
 :: (Field_ r, IsString r)
 => Comp (VarField (Compound r) t) r -> Comp t r
fromVarFieldM = fromVarM . fromFieldM pure


-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
-- * Let path pattern (leaf pattern assigns matched value to path)
-- * Block pattern (matches a set of paths to nested (lifted) patterns)
-- * An block pattern with left over pattern (matches set of fields not
--   matched by the block pattern)
type BlockPath_ r = (Block_ r, Path_ r)

parseBlockPath
 :: BlockPath_ r => Parser (Stmt r) -> Parser r
parseBlockPath ps =
  parsePath
    <|> parseBlock ps

type BlockPath s c t = Block s <: VarField c  t

fromBlockPathM
 :: BlockPath_ r
 => Comp (BlockPath (Stmt r) (Compound r) t) r -> Comp t r
fromBlockPathM = fromVarFieldM . fromBlockM pure

 
type Pun_ s = (Let_ s, Path_ s, Path_ (Lhs s))

parsePun :: Pun_ s => Parser (Rhs s) -> Parser s
parsePun pr = do
  p <- parsePath
  (do
    eq <- parseLet
    r <- pr
    return (clonePath p `eq` r))
    <|> return (clonePath p)
  
clonePath
 :: (Field_ r, IsString r)
 => Comp (VarField (Compound r) Null) Void -> r
clonePath = handleAll fromVarFieldM

type Pun c r t =
  Let (Comp (VarField c Null) Void) r <: VarField c t

fromPunM
 :: Pun_ s => Comp (Pun (Compound s) (Rhs s) t) s -> Comp t s
fromPunM =
  fromVarFieldM . fromLetM (handleAll fromVarFieldM) pure

type Pattern_ p = (BlockPath_ p, BlockExt_ p, Stmt p ~ Stmt (Ext p))

parsePattern :: Pattern_ p => Parser (Stmt p) -> Parser p
parsePattern ps = do
  p <- parseBlockPath ps
  f <- parseBlockExt ps
  return (f p)

type Pattern s c t = BlockPath s c (BlockExt s t)

fromPatternM
 :: Pattern_ p
 => Comp (Pattern (Stmt p) (Compound p) t) p -> Comp t p
fromPatternM = fromBlockExtM . fromBlockPathM

-- | Proof of instance 'Pattern_ (Comp (Pattern s c t) a)' with 'Stmt (Comp (Pattern s c t) a) ~ s' and 'Compound (Comp (Pattern s c t) a) ~ c'
patternMProof
 :: (Chain_ c, IsString c)
 => Comp (Pattern s c Null) Void -> Comp (Pattern s c t) a
patternMProof = handleAll fromPatternM

type Match_ s = (Pun_ s, Pattern_ (Rhs s), s ~ Stmt (Rhs s))

parseMatch :: Match_ s => Parser s
parseMatch = parsePun (parsePattern parseMatch)


-- | Let pattern statement (define a pattern to be equal to a value)
type Rec_ s = (Let_ s, Path_ s, Pattern_ (Lhs s))

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
      f <- parseBlockExt pls
      eq <- parseLet
      rhs <- pr
      return (f (clonePath p) `eq` rhs)) <|>
      return (clonePath p)

type Rec ls r c t =
  Let (Comp (Pattern ls c Null) Void) r <: VarField c t

fromRecM
 :: Rec_ s
 => Comp (Rec (Stmt (Lhs s)) (Rhs s) (Compound s) t) s -> Comp t s
fromRecM =
  fromVarFieldM . fromLetM (handleAll fromPatternM) pure

-- | Proof of 'Rec_ (Comp (Rec ls r c t) a)' where 'Stmt (Lhs (Comp (Rec ls r c t) a)) ~ ls', 'Rhs (Comp (Rec ls r c t) a) ~ r', and 'Compound (Comp (Rec ls r c t) a) ~ c'.
recMProof
 :: (IsString c, Chain_ c)
 => Comp (Rec ls r c Null) Void -> Comp (Rec ls r c t) a
recMProof = handleAll fromRecM


type Defn_ s =
  ( Rec_ s, Match_ (Stmt (Lhs s))
  , Expr_ (Rhs s), Stmt (Rhs s) ~ s
  )

parseDefn :: Defn_ s => Parser s
parseDefn = parseRec parseMatch (parseExpr parseDefn)
