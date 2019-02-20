{-# LANGUAGE RankNTypes, TypeOperators, ConstraintKinds, TypeFamilies, FlexibleContexts, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Goat.Lang.Expr
  where

import Goat.Comp
import Goat.Lang.Comment (spaces)
import Goat.Lang.Block
import Goat.Lang.LogicB
import Goat.Lang.CmpB
import Goat.Lang.ArithB
import Goat.Lang.Unop
import Goat.Lang.Extend
import Goat.Lang.Field
import Goat.Lang.Extern
import Goat.Lang.Text
import Goat.Lang.Number
import Goat.Lang.Ident
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))


type Lit_ r =
  ( Text_ r, Fractional r, IsString r, Extern_ r, Block_ r )
  
parseLit :: Lit_ r => Parser (Stmt r) -> Parser r
parseLit ps =
  parseText                     -- '"' ...
    <|> parseNumber             -- digit ...
    <|> (parseIdent <* spaces)  -- alpha ...
    <|> parseExtern             -- '@' ...
    <|> parseBlock ps           -- '{' ... 
  
newtype SomeLit stmt =
  SomeLit {
    getLit
     :: forall t a
      . Comp 
          (Text <:
          Number <:
          Var <:
          Extern <:
          Block stmt <:
          t)
          a
    }

instance Text_ (SomeLit stmt) where
  quote_ s = SomeLit (quote_ s)

instance Num (SomeLit stmt) where
  fromInteger i = SomeLit (fromInteger i)
  SomeLit a + SomeLit b = SomeLit (a + b)
  SomeLit a * SomeLit b = SomeLit (a * b)
  negate (SomeLit a) = SomeLit (negate a)
  abs (SomeLit a) = SomeLit (abs a)
  signum (SomeLit a) = SomeLit (abs a)
  
instance Fractional (SomeLit stmt) where
  fromRational i = SomeLit (fromRational i)
  recip (SomeLit a) = SomeLit (recip a)

instance IsString (SomeLit stmt) where
  fromString s = SomeLit (fromString s)

instance Extern_ (SomeLit stmt) where
  use_ i = SomeLit (use_ i)

instance Block_ (SomeLit stmt) where
  type Stmt (SomeLit stmt) = stmt
  block_ bdy = SomeLit (block_ bdy)

showLit
 :: (stmt -> ShowS) -> SomeLit stmt -> Comp t ShowS
showLit ss =
  showBlock ss
    . showExtern
    . showVar
    . showNumber
    . showText
    . getLit

fromLit
 :: Lit_ r => (stmt -> Stmt r) -> SomeLit stmt -> Comp t r
fromLit ks =
  fromBlock ks
    . fromExtern
    . fromVar
    . fromNumber
    . fromText
    . getLit

litProof :: SomeLit s -> SomeLit s
litProof = run . fromLit id

-- | Expression with operator precedence
type Op_ r =
  ( LogicB_ r, ArithB_ r, CmpB_ r, Unop_ r )
  
parseOp
 :: Op_ r => Parser r -> Parser r
parseOp p =
  parseLogicB
    (parseCmpB
      (parseArithB
        (parseUnop <*> (p <|> parens (parseOp p)))))
  where
    parens :: Parser a -> Parser a
    parens =
      Parsec.between
        (Parsec.char '(' >> spaces)
        (Parsec.char ')' >> spaces)

newtype SomeOp =
  SomeOp {
    getOp
     :: forall t a 
      . Comp (LogicB <: CmpB <: ArithB <: Unop <: t) a
    }

instance LogicB_ SomeOp where
  SomeOp a #|| SomeOp b = SomeOp (a #|| b)
  SomeOp a #&& SomeOp b = SomeOp (a #&& b)
    
instance CmpB_ SomeOp where
  SomeOp a #== SomeOp b = SomeOp (a #== b)
  SomeOp a #!= SomeOp b = SomeOp (a #!= b)
  SomeOp a #<  SomeOp b = SomeOp (a #<  b)
  SomeOp a #<= SomeOp b = SomeOp (a #<= b)
  SomeOp a #>  SomeOp b = SomeOp (a #>  b)
  SomeOp a #>= SomeOp b = SomeOp (a #>= b)

instance ArithB_ SomeOp where
  SomeOp a #+ SomeOp b = SomeOp (a #+ b)
  SomeOp a #- SomeOp b = SomeOp (a #- b)
  SomeOp a #* SomeOp b = SomeOp (a #* b)
  SomeOp a #/ SomeOp b = SomeOp (a #/ b)
  SomeOp a #^ SomeOp b = SomeOp (a #^ b)

instance Unop_ SomeOp where
  neg_ (SomeOp a) = SomeOp (neg_ a)
  not_ (SomeOp a) = SomeOp (not_ a)

showOp :: SomeOp -> Comp t ShowS
showOp =
  showUnop
    . showArithB
    . showCmpB
    . showLogicB
    . getOp

fromOp :: Op_ r => SomeOp -> Comp t r
fromOp =
  fromUnop
    . fromArithB
    . fromCmpB
    . fromLogicB
    . getOp

opProof :: SomeOp -> SomeOp
opProof = run . fromOp


-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type Expr_ r =
  ( Chain_ r, Lit_ r, Op_ r, ExtendBlock_ r )
  -- r, Compound r, Stmt r, Ext r

-- | Parse a chain of field accesses and extensions
parseExpr
 :: Expr_ r => Parser (Stmt r) -> Parser r
parseExpr ps = parseOp (term ps)
  where
    term ps = do
      e <- first ps
      k <- rest ps
      return (k e)

    rest ps = go id where 
      go k = (do
        k' <- step ps
        go (k' . k))
        <|> return k
    
    step ps = (do
      ext <- parseExtend
      b <- parseBlock ps
      return (`ext` b))     -- '{' ...
        <|> parseField      -- '.' ...
    
    first ps =
      parseRel            -- '.' alpha 
        <|> parseLit ps   -- '"' ...
                          -- digit ...
                          -- alpha ...
                          -- '@' ...
                          -- '{' ...  
        
    parseRel = do 
      s <- parseSelf
      f <- parseField
      return (f s)
        

newtype SomeExpr stmt =
  SomeExpr {
    getExpr
     :: forall t a
      . Comp
          (Field (SomeExpr stmt) <:
          Text <:
          Number <:
          Var <:
          Extern <:
          Block stmt <:
          Extend (SomeBlock stmt) <:
          ArithB <:
          CmpB <:
          LogicB <:
          Unop <:
          t)
          a
    }

instance Field_ (SomeExpr stmt) where
  type Compound (SomeExpr stmt) = SomeExpr stmt
  c #. i = SomeExpr (c #. i)

instance Text_ (SomeExpr stmt) where
  quote_ s = SomeExpr (quote_ s)

instance Num (SomeExpr stmt) where
  fromInteger i = SomeExpr (fromInteger i)
  SomeExpr a + SomeExpr b = SomeExpr (a + b)
  SomeExpr a * SomeExpr b = SomeExpr (a * b)
  abs (SomeExpr a) = SomeExpr (abs a)
  signum (SomeExpr a) = SomeExpr (signum a)
  negate (SomeExpr a) = SomeExpr (negate a)

instance Fractional (SomeExpr stmt) where
  fromRational i = SomeExpr (fromRational i)
  recip (SomeExpr a) = SomeExpr (recip a)

instance IsString (SomeExpr stmt) where
  fromString s = SomeExpr (fromString s)

instance Extern_ (SomeExpr stmt) where
  use_ s = SomeExpr (use_ s)

instance Block_ (SomeExpr stmt) where
  type Stmt (SomeExpr stmt) = stmt
  block_ s = SomeExpr (block_ s)

instance Extend_ (SomeExpr stmt) where
  type Ext (SomeExpr stmt) = SomeBlock stmt
  SomeExpr ex # x = SomeExpr (ex # x)

instance ArithB_ (SomeExpr stmt) where
  SomeExpr a #+ SomeExpr b = SomeExpr (a #+ b)
  SomeExpr a #- SomeExpr b = SomeExpr (a #- b)
  SomeExpr a #* SomeExpr b = SomeExpr (a #* b)
  SomeExpr a #/ SomeExpr b = SomeExpr (a #/ b)
  SomeExpr a #^ SomeExpr b = SomeExpr (a #^ b)

instance CmpB_ (SomeExpr stmt) where
  SomeExpr a #== SomeExpr b = SomeExpr (a #== b)
  SomeExpr a #!= SomeExpr b = SomeExpr (a #!= b)
  SomeExpr a #>  SomeExpr b = SomeExpr (a #>  b)
  SomeExpr a #>= SomeExpr b = SomeExpr (a #>= b)
  SomeExpr a #<  SomeExpr b = SomeExpr (a #<  b)
  SomeExpr a #<= SomeExpr b = SomeExpr (a #<= b)

instance LogicB_ (SomeExpr stmt) where
  SomeExpr a #|| SomeExpr b = SomeExpr (a #|| b)
  SomeExpr a #&& SomeExpr b = SomeExpr (a #&& b)

instance Unop_ (SomeExpr stmt) where
  neg_ (SomeExpr a) = SomeExpr (neg_ a)
  not_ (SomeExpr a) = SomeExpr (not_ a)

showExpr
 :: (stmt -> ShowS) -> SomeExpr stmt -> Comp t ShowS
showExpr ss =
  showUnop
    . showLogicB
    . showCmpB
    . showArithB
    . showExtend (run . showBlock ss . getBlock)
    . showBlock ss
    . showExtern
    . showVar
    . showNumber
    . showText
    . showField (run . showExpr ss)
    . getExpr

fromExpr
 :: Expr_ r => (stmt -> Stmt r) -> SomeExpr stmt -> Comp t r
fromExpr ks =
  fromUnop
    . fromLogicB
    . fromCmpB
    . fromArithB
    . fromExtend (run . fromBlock ks . getBlock)
    . fromBlock ks
    . fromExtern
    . fromVar
    . fromNumber
    . fromText
    . fromField (run . fromExpr ks)
    . getExpr


exprProof :: SomeExpr s -> SomeExpr s
exprProof = run . fromExpr id
