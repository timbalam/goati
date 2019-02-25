{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, FlexibleInstances, RankNTypes #-}
module Goat.Lang.Let
  where
  
import Goat.Comp
import Goat.Lang.Symbol
import Goat.Lang.Ident
import Goat.Lang.Field
import Goat.Lang.Extend
import Goat.Lang.Expr
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

instance MemberU2 Let r => Let_ (Comp r a) where
  type Lhs (Comp r a) = Dep1 Let r
  type Rhs (Comp r a) = Dep2 Let r
  l #= r = send (l :#= r)

showLet
 :: (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> Comp (Let lhs rhs <: t) ShowS -> Comp t ShowS
showLet sl sr = handle (\ (l :#= r) _ ->
  return
    (sl l . showChar ' ' . showSymbol "=" . showChar ' ' . sr r))

fromLet
 :: Let_ s
 => (lhs -> Lhs s)
 -> (rhs -> Rhs s)
 -> Comp (Let lhs rhs <: t) s -> Comp t s
fromLet kl kr = handle (\ (l :#= r) _ ->
  return (kl l #= kr r))

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
