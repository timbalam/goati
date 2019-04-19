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
import Data.String (IsString)
import Data.Void (Void, absurd)

-- | Nested field accesses
type VarField_ r = (Field_ r, IsString r)
type VarFieldChain_ r = (Field_ r, IsString r, Compound r ~  r)

parseVarPath
 :: (VarField_ r, VarFieldChain_ (Compound r)) => Parser r
parseVarPath = 
  (do
    s <- parseIdent
    (do 
      f <- parseFieldLink
      return (f (fromString s))) <|>
      return (fromString s)) <|>
    (do
      s <- parseSelf
      f <- parseFieldLink
      return (f (fromSelf s)))

type VarField c t = Field c <: Var <: t

fromVarFieldM
 :: VarField_ r => Comp (VarField (Compound r) t) r -> Comp t r
fromVarFieldM = fromVarM . fromFieldM pure


-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
-- * Let path pattern (leaf pattern assigns matched value to path)
-- * Block pattern (matches a set of paths to nested (lifted) patterns)
-- * An block pattern with left over pattern (matches set of fields not
--   matched by the block pattern)
type Pun_ s =
  (Let_ s, VarField_ s, VarField_ (Lhs s), Compound s ~ Compound (Lhs s))

parsePun
 :: (Pun_ s, VarFieldChain_ (Compound s)) => Parser (Rhs s) -> Parser s
parsePun pr = do
  p <- parseVarPath
  (do
    eq <- parseLet
    r <- pr
    return (cloneVarField p `eq` r))
    <|> return (cloneVarField p)
  
cloneVarField
 :: (Field_ r, IsString r)
 => Comp (VarField (Compound r) Null) Void -> r
cloneVarField = handleAll fromVarFieldM

type Pun c r t =
  Let (Comp (VarField c Null) Void) r <: VarField c t

fromPunM
 :: Pun_ s => Comp (Pun (Compound s) (Rhs s) t) s -> Comp t s
fromPunM =
  fromVarFieldM . fromLetM (handleAll fromVarFieldM) pure

  
type Pattern_ p = (VarField_ p, Extend_ p, Block_ p)

type PatternChain_ c e x s =
  ( Field_ e, IsString e, Block_ e, Extend_ e
  , Field_ c, IsString c
  , Block_ x
  , Compound e ~ c, Ext e ~ e, Extension e ~ x, Stmt e ~ s
  , Compound c ~ c
  , Stmt x ~ s
  )

type Pattern c e x s t =
  Field c <: Extend e x <: Var <: Block s <: t

fromPatternM
 :: Pattern_ p
 => Comp (Pattern (Compound p) (Ext p) (Extension p) (Stmt p) t) p -> Comp t p
fromPatternM =
  fromBlockM pure .
    fromVarM .
    fromExtendM pure pure .
    fromFieldM pure


-- | Let pattern statement (define a pattern to be equal to a value)
type Match_ s =
  ( Pun_ s, Pattern_ (Rhs s)
  , VarFieldChain_ s
  , PatternChain_ (Compound (Rhs s)) (Ext (Rhs s)) (Extension (Rhs s)) (Stmt (Rhs s))
  , Stmt (Rhs s) ~ s
  )

parseDecomp
 :: (Block_ s, Match_ (Stmt s)) => Parser s
parseDecomp =
  parseBlock
    (parsePun
      (do
        p <- parseVarPath
        f <-
          (do 
            g <- parseExtendLink parseDecomp
            return (g . cloneVarField)) <|>
            pure cloneVarField
        return (f p)))

type Rec_ s =
  (Let_ s, VarField_ s, Pattern_ (Lhs s), Compound s ~ Compound (Lhs s))
type RecChain_ c e x s =
  (PatternChain_ c e x s, VarFieldChain_ c, Match_ s)

-- | Parse a statement of a block expression
parseRec
 :: ( Rec_ s
    , RecChain_ (Compound s) (Ext (Lhs s)) (Extension (Lhs s)) (Stmt (Lhs s))
    )
 => Parser (Rhs s)
 -> Parser s
parseRec pr =
  do
    p <- parseVarPath
    (do
      f <- 
        (do
          g <- parseExtendLink parseDecomp
          return (g . cloneVarField)) <|>
          pure cloneVarField
      eq <- parseLet
      rhs <- pr
      return (f p `eq` rhs)) <|>
      return (cloneVarField p)

type Rec c e x s r t =
  Let (Comp (Pattern c e x s Null) Void) r <: VarField c t

fromRecM
 :: Rec_ s
 => Comp
      (Rec (Compound s) (Ext (Lhs s)) (Extension (Lhs s)) (Stmt (Lhs s)) (Rhs s) t)
      s
 -> Comp t s
fromRecM =
  fromVarFieldM . fromLetM (pure . handleAll fromPatternM) pure

-- | Proof of '(Stmt (Lhs (Comp (Rec c e x s r t) a)) ~ s, Rhs (Comp (Rec c e x s r t) a) ~ r', Compound (Comp (Rec c e x s r t) a) ~ c, Ext (Comp (Rec c e x s r t) a) ~ e, Extension (Comp (Rec c e x s r t) a) ~ x) => Rec_ (Comp (Rec c e x s r t) a)' instance
recMProof
 :: Comp (Rec c e x s r Null) Void -> Comp (Rec c e x s r t) a
recMProof = handleAll fromRecM


type Defn_ s =
  ( Rec_ s, Expr_ (Rhs s)
  , RecChain_ (Compound s) (Ext (Lhs s)) (Extension (Lhs s)) (Stmt (Lhs s))
  , ExprChain_ (Compound (Rhs s)) (Ext (Rhs s)) (Extension (Rhs s)) (Stmt (Rhs s))
  , Stmt (Rhs s) ~ s
  )

parseDefn :: Defn_ s => Parser s
parseDefn = parseRec (parseExpr parseDefn)
