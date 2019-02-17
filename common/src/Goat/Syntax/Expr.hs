{-# LANGUAGE RankNTypes, TypeOperators, ConstraintKinds, TypeFamilies, FlexibleContexts, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Goat.Syntax.Expr
  where

import Goat.Co
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Block
import Goat.Syntax.LogicB
import Goat.Syntax.CmpB
import Goat.Syntax.ArithB
import Goat.Syntax.Unop
import Goat.Syntax.Extend
import Goat.Syntax.Field
import Goat.Syntax.Extern
import Goat.Syntax.Text
import Goat.Syntax.Number
import Goat.Syntax.Ident
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
    -- <|> (esc <*> first)      -- '^' ...
    -- <|> parens p             -- '(' ...
    <|> parseBlock ps           -- '{' ... 
  
newtype SomeLit stmt =
  SomeLit {
    getLit
     :: forall t a
      . Comp 
          (Text <:
          Number <:
          Ident <:
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
    . showIdent
    . showNumber
    . showText
    . getLit

fromLit
 :: Lit_ r => (stmt -> Stmt r) -> SomeLit stmt -> Comp t r
fromLit ks =
  fromBlock ks
    . fromExtern
    . fromIdent
    . fromNumber
    . fromText
    . getLit

litProof :: SomeLit s -> SomeLit s
litProof = run . fromLit

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
  showCmpB
    . showArithB
    . showLogicB
    . getOp

fromOp :: Op_ r => SomeOp -> Comp t r
fromOp =
  fromCmpB
    . fromArithB
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
parseExpr ps = do
  e <- first
  k <- rest
  return (k e)
  where
    rest = go id where 
      go k = (do
        k' <- step 
        go (k' . k))
        <|> return k
    
    step = (do
      ext <- parseExtend
      b <- parseBlock ps
      return (`ext` b))     -- '{' ...
        <|> parseField      -- '.' ...
    
    first =
      parseRel          -- '.' alpha 
        <|> parseLit    -- '"' ...
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
          Self <:
          Ident <:
          Extern <:
          Block stmt <:
          Extend (SomeBlock stmt) <:
          ArithB <:
          CmpB <:
          LogicB <:
          t)
          a
    }

showExpr
 :: (stmt -> ShowS) -> SomeExpr stmt -> Comp t ShowS
showExpr ss =
  showLogicB
    . showCmpB
    . showArithB
    . showExtend (run . showBlock ss)
    . showBlock ss
    . showExtern
    . showIdent
    . showSelf
    . showNumber
    . showText
    . showField (run . showExpr)
    . getExpr

fromExpr
 :: Expr_ r => (stmt -> Stmt r) -> SomeExpr stmt -> Comp t r
fromExpr ks =
  fromLogicB
    . fromCmpB
    . fromArithB
    . fromExtend (run . fromBlock ks)
    . fromBlock ks
    . fromExtern
    . fromIdent
    . fromSelf
    . fromNumber
    . fromText
    . fromField (run . fromExpr)
    . getExpr


exprProof :: SomeExpr s -> SomeExpr s
exprProof = run . fromExpr id
