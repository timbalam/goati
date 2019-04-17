module Goat.Lang.Match
  where

import Goat.Lang.Ident
import Goat.Lang.Field
import Goat.Lang.Extend
import Goat.Lang.Expr
import Text.Parsec ((<|>))
import Data.String (IsString(..))
import Data.Void (Void, absurd)

type Match_ s =
  ( Let_ s, Path_ s, Path_ (Lhs s)
  , ExtendBlock_ (Rhs s), Path_ (Rhs s), Stmt (Rhs s) ~ s
  )

parseMatch :: Match_ s => Parser s
parseMatch = do
  p <- parsePath
  (do
    eq <- parseLet
    r <- parsePatt
    return (run (fromPath p) `eq` r))
    <|> return (run (fromPath p))
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


newtype SomeMatch = 
  SomeMatch {
    getMatch
     :: forall t a
      . Comp
          (Let
            SomePath
            (SomePathExtendBlock SomeMatch) <:
          Field SomeVarChain <:
          Var <:
          t)
          a
    }

instance Let_ SomeMatch where
  type Lhs SomeMatch = SomePath
  type Rhs SomeMatch = SomePathExtendBlock SomeMatch
  l #= r = SomeMatch (l #= r)

instance Field_ SomeMatch where
  type Compound SomeMatch = SomeVarChain
  c #. i = SomeMatch (c #. i)
  
instance IsString SomeMatch where
  fromString s = SomeMatch (fromString s)

showMatch
 :: SomeMatch -> Comp t ShowS
showMatch =
  showVar
    . showField (run . showVarChain)
    . showLet
        (run . showPath)
        (run . showPathExtendBlock (run . showMatch))
    . getMatch

fromMatch
 :: Match_ s
 => SomeMatch -> Comp t s
fromMatch = 
  fromVar
    . fromField (run . fromVarChain)
    . fromLet
        (run . fromPath)
        (run . fromPathExtendBlock (run . fromMatch))
    . getMatch

matchProof :: SomeMatch -> SomeMatch
matchProof = run . fromMatch


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
      return (ext (run (fromPath p)) `eq` rhs))
      <|> return (run (fromPath p))
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

newtype SomeRec lstmt rhs =
  SomeRec {
    getRec
     :: forall t a
      . Comp
          (Let
            (SomePathExtendBlock lstmt)
            rhs <:
          Field SomeVarChain <:
          Var <:
          t)
          a
    }

instance Let_ (SomeRec lstmt rhs) where
  type Lhs (SomeRec lstmt rhs) = SomePathExtendBlock lstmt
  type Rhs (SomeRec lstmt rhs) = rhs
  l #= r = SomeRec (l #= r)

instance Field_ (SomeRec lstmt rhs) where
  type Compound (SomeRec lstmt rhs) = SomeVarChain
  c #. i = SomeRec (c #. i)

instance IsString (SomeRec lstmt rhs) where
  fromString s = SomeRec (fromString s)

showRec
 :: (lstmt -> ShowS)
 -> (rhs -> ShowS)
 -> SomeRec lstmt rhs -> Comp t ShowS
showRec sls sr =
  showVar
    . showField (run . showVarChain)
    . showLet
        (run . showPathExtendBlock sls)
        sr
    . getRec

fromRec
 :: Rec_ s
 => (lstmt -> Stmt (Lhs s))
 -> (rhs -> Rhs s)
 -> SomeRec lstmt rhs -> Comp t s
fromRec kls kr =
  fromVar
    . fromField (run . fromVarChain)
    . fromLet
        (run . fromPathExtendBlock kls)
        kr
    . getRec

recProof :: SomeRec lstmt rhs -> SomeRec lstmt rhs
recProof = run . fromRec id id


type Defn_ s =
  ( Rec_ s, Match_ (Stmt (Lhs s))
  , Expr_ (Rhs s), Stmt (Rhs s) ~ s
  )

parseDefn :: Defn_ s => Parser s
parseDefn = parseRec parseMatch (parseExpr parseDefn)

newtype SomeDefn =
  SomeDefn {
    getDefn
     :: forall t a
      . Comp
          (Let
            (SomePathExtendBlock SomeMatch)
            (SomeExpr SomeDefn) <:
            Field SomeVarChain <:
            Var <:
            t)
          a
    }

instance Field_ SomeDefn where
  type Compound SomeDefn = SomeVarChain
  c #. i = SomeDefn (c #. i)

instance IsString SomeDefn where
  fromString s = SomeDefn (fromString s)

instance Let_ SomeDefn where
  type Lhs SomeDefn = SomePathExtendBlock SomeMatch
  type Rhs SomeDefn = SomeExpr SomeDefn
  l #= r = SomeDefn (l #= r)
    
showDefn :: SomeDefn -> Comp t ShowS
showDefn =
  showVar
    . showField (run . showVarChain)
    . showLet
        (run . showPathExtendBlock (run . showMatch))
        (run . showExpr (run . showDefn))
    . getDefn

fromDefn :: Defn_ s => SomeDefn -> Comp t s
fromDefn =
  fromVar
    . fromField (run . fromVarChain)
    . fromLet
        (run . fromPathExtendBlock (run . fromMatch))
        (run . fromExpr (run . fromDefn))
    . getDefn

defnProof :: SomeDefn -> SomeDefn
defnProof = run . fromDefn



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

showPathExtendBlock
 :: (forall x . (x -> ShowS) -> stmt x -> ShowS)
 -> Comp (PathExtendBlock stmt t) ShowS -> Comp t ShowS
showPathExtendBlock ss =
  showField (run . showVarChain)
    . showVar
    . showBlockC (ss id)
    . showExtendC (showBlock . ss)

fromPathExtendBlock
 :: (ExtendBlock_ r, Path_ r)
 => (stmt -> Stmt r) 
 -> SomePathExtendBlock stmt -> Comp t r
fromPathExtendBlock ks =
  fromField (run . fromVarChain)
    . fromVar
    . fromBlock (ks id)
    . fromExtend (fromBlock . ks)

pathExtendBlockProof
 :: SomePathExtendBlock stmt -> SomePathExtendBlock stmt
pathExtendBlockProof = run . fromPathExtendBlock id
-}
