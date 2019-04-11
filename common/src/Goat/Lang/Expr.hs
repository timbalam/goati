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
import Data.Void (Void)


type Lit_ r =
  ( Text_ r, Fractional r, IsString r, Extern_ r, Block_ r )
  
parseLit :: Lit_ r => Parser (Stmt r) -> Parser r
parseLit ps =
  parseText                     -- '"' ...
    <|> parseNumber             -- digit ...
    <|> (parseIdent <* spaces)  -- alpha ...
    <|> parseExtern             -- '@' ...
    <|> parseBlock ps           -- '{' ... 

type Lit stmt t =
  Text <: Number <: Var <: Extern <: Block stmt <: t

showLit
 :: Traversable stmt
 => (stmt ShowS -> ShowS)
 -> Comp (Lit stmt t) ShowS -> Comp t ShowS
showLit ss =
  showBlock ss .
    showExtern .
    showVar .
    showNumber .
    showText

fromLit
 :: (Traversable stmt, Lit_ r)
 => (stmt r -> Stmt r)
 -> Comp (Lit stmt t) r -> Comp t r
fromLit ks =
  fromBlock ks .
    fromExtern .
    fromVar .
    fromNumber .
    fromText

litProof
 :: Traversable s => Comp (Lit s Null) Void -> Comp (Lit s t) a
litProof = handleAll (fromLit id)

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

type Op t = LogicB <: CmpB <: ArithB <: Unop <: t
type SomeOp = Comp (Op Null) Void

showOp :: Comp (Op t) ShowS -> Comp t ShowS
showOp =
  showUnop .
    showArithB .
    showCmpB .
    showLogicB

fromOp :: Op_ r => Comp (Op t) r -> Comp t r
fromOp =
  fromUnop .
    fromArithB .
    fromCmpB .
    fromLogicB

opProof :: SomeOp -> Comp (Op t) a
opProof = handleAll fromOp


-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type Expr_ r =
  ( Field_ r, Chain_ (Compound r)
  , Lit_ r, Lit_ (Compound r)
  , Op_ r, Op_ (Compound r)
  , ExtendBlock_ r, ExtendBlock_ (Compound r)
  , Ext r ~ Ext (Compound r)
  )
  -- r, Compound r, Stmt r, Ext r

-- | Parse a chain of field accesses and extensions
parseExpr
 :: Expr_ r => Parser (Stmt r) -> Parser r
parseExpr ps = parseOp (term ps)
  where
    term ps =
      (do
        a <- parseLit ps
        f <- parseBlocks ps
        (fieldNext ps (runLit (f a))
          <|> return (runLit (f a)))
        <|> fieldNext ps (fromString ""))
    
    runLit
     :: (Lit_ r, Extend_ r)
     => Union (Lit (Stmt r) (Extend (Ext r) <: Null)) r
     -> r
    runLit = fromExtendU id (fromLitU id voidU)
    
    fieldNext
     :: (Field_ r, Chain_ (Compound r), Extend_ r, Block_ (Ext r))
     => Parser (Stmt r) -> Compound r -> Parser r
    fieldNext ps c = do
      f <- parseField
      g <- parseBlocks ps
      (fieldNext ps (runField (g (f c)))
        <|> r (runField (g (f c))))
    
    runField
     :: (Field_ r, Extend_ r)
     => Comp (Field (Compound r) <: Extend (Ext r) <: Null) Void
     -> r
    runField = handleAll (fromExtend id . fromField id)
    
    parseBlocks
     :: (Extend_ r, Block_ (Ext r))
     => Parser (Stmt (Ext r)) -> Parser (r -> r)
    parseBlocks ps = go id where
      go k = (do
        ext <- parseExtend
        b <- parseBlock ps
        go (\ r -> ext (k r) b))
        <|> return k
        
  {-
    term ps = do
      e <- first ps
      k <- rest ps
      return (k e)

    rest :: Parser (Stmt r) -> Parser (Compound r -> r)
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
    
    first
     :: (Lit_ r, Field_ r, IsString (Compound r))
     => Parser (Stmt r)
     -> Parser r
    first ps =
      parseRel            -- '.' alpha 
        <|> parseLit ps   -- '"' ...
                          -- digit ...
                          -- alpha ...
                          -- '@' ...
                          -- '{' ...  
    
    parseRel
     :: (Field_ r, IsString (Compound r))
     => Parser r
    parseRel = do 
      s <- parseSelf
      f <- parseField
      return (f s)
  -}

type Expr' cmp stmt t =
  Field cmp <:
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
    t

type ExprChain stmt t a = Expr' a stmt t a 

showExprChain
 :: (stmt -> ShowS)
 -> Comp (ExprChain stmt t) ShowS
 -> Comp t ShowS
showExprChain ss =
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
    . showField (run . showExprChain ss)

fromExprChain
 :: (Lit_ r, Op_ r, ExtendBlock_ r, Chain_ r)
 => (stmt -> Stmt r) -> SomeExprChain stmt -> Comp t r
fromExprChain ks =
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
    . fromField (run . fromExprChain ks)
    . getExprChain


exprChainProof :: SomeExprChain s -> SomeExprChain s
exprChainProof = run . fromExprChain id

{-
newtype SomeExprChain stmt =
  SomeExprChain {
    getExprChain
     :: forall t a .
          Comp
            (Field (SomeExprChain stmt) <:
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

instance Field_ (SomeExprChain stmt) where
  type Compound (SomeExprChain stmt) = SomeExprChain stmt
  c #. i = SomeExprChain (c #. i)

instance Text_ (SomeExprChain stmt) where
  quote_ s = SomeExprChain (quote_ s)

instance Num (SomeExprChain stmt) where
  fromInteger i = SomeExprChain (fromInteger i)
  SomeExprChain a + SomeExprChain b = SomeExprChain (a + b)
  SomeExprChain a * SomeExprChain b = SomeExprChain (a * b)
  abs (SomeExprChain a) = SomeExprChain (abs a)
  signum (SomeExprChain a) = SomeExprChain (signum a)
  negate (SomeExprChain a) = SomeExprChain (negate a)

instance Fractional (SomeExprChain stmt) where
  fromRational i = SomeExprChain (fromRational i)
  recip (SomeExprChain a) = SomeExprChain (recip a)

instance IsString (SomeExprChain stmt) where
  fromString s = SomeExprChain (fromString s)

instance Extern_ (SomeExprChain stmt) where
  use_ s = SomeExprChain (use_ s)

instance Block_ (SomeExprChain stmt) where
  type Stmt (SomeExprChain stmt) = stmt
  block_ s = SomeExprChain (block_ s)

instance Extend_ (SomeExprChain stmt) where
  type Ext (SomeExprChain stmt) = SomeBlock stmt
  SomeExprChain ex # x = SomeExprChain (ex # x)

instance ArithB_ (SomeExprChain stmt) where
  SomeExprChain a #+ SomeExprChain b = SomeExprChain (a #+ b)
  SomeExprChain a #- SomeExprChain b = SomeExprChain (a #- b)
  SomeExprChain a #* SomeExprChain b = SomeExprChain (a #* b)
  SomeExprChain a #/ SomeExprChain b = SomeExprChain (a #/ b)
  SomeExprChain a #^ SomeExprChain b = SomeExprChain (a #^ b)

instance CmpB_ (SomeExprChain stmt) where
  SomeExprChain a #== SomeExprChain b = SomeExprChain (a #== b)
  SomeExprChain a #!= SomeExprChain b = SomeExprChain (a #!= b)
  SomeExprChain a #>  SomeExprChain b = SomeExprChain (a #>  b)
  SomeExprChain a #>= SomeExprChain b = SomeExprChain (a #>= b)
  SomeExprChain a #<  SomeExprChain b = SomeExprChain (a #<  b)
  SomeExprChain a #<= SomeExprChain b = SomeExprChain (a #<= b)

instance LogicB_ (SomeExprChain stmt) where
  SomeExprChain a #|| SomeExprChain b = SomeExprChain (a #|| b)
  SomeExprChain a #&& SomeExprChain b = SomeExprChain (a #&& b)

instance Unop_ (SomeExprChain stmt) where
  neg_ (SomeExprChain a) = SomeExprChain (neg_ a)
  not_ (SomeExprChain a) = SomeExprChain (not_ a)
-}
        

newtype SomeExpr stmt =
  SomeExpr {
    getExpr
     :: forall t a
      . Comp
          (Field (SomeExprChain stmt) <:
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
  type Compound (SomeExpr stmt) = SomeExprChain stmt
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
    . showField (run . showExprChain ss)
    . getExpr

fromExpr
 :: Expr_ r => (stmt -> Stmt r) -> SomeExpr stmt -> Comp t r
fromExpr ks =
  fromUnop .
    fromLogicB .
    fromCmpB .
    fromArithB .
    fromExtend (run . fromBlock ks . getBlock) .
    fromBlock ks .
    fromExtern .
    fromVar .
    fromNumber .
    fromText .
    fromField (run . fromExprChain ks) .
    getExpr


exprProof :: SomeExpr s -> SomeExpr s
exprProof = run . fromExpr id
