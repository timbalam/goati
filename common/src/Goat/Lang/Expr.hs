{-# LANGUAGE RankNTypes, TypeOperators, ConstraintKinds, TypeFamilies, FlexibleContexts, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Goat.Lang.Expr
  where

-- import Goat.Comp
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
import Goat.Lang.Reflect
import Control.Monad (>=>)
import Data.Void (Void)
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))


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

showOpM
 :: Applicative m
 => Comp (Op t) ShowS -> Comp t ShowS
showOpM =
  liftPrec showUnopMPrec .
    liftPrec showArithBMPrec .
    liftPrec showCmpBMPrec .
    liftPrec showLogicBMPrec .
    showNested showOpM
  where
    liftPrec
     :: ((Comp t ShowS -> m ShowS) -> Comp t ShowS -> m ShowS)
     -> (Comp (h <: t) ShowS -> m ShowS)
     -> Comp (h <: t) ShowS -> m ShowS
    liftPrec lsp sp = lsp (sp . raise)
    
    showNested
     :: Applicative m
     => (Comp (Op t) ShowS -> Comp t ShowS)
     -> Comp (Op t) ShowS -> Comp t ShowS
    showNested sp (Done a) = pure a
    showNested sp (Req r k)
      | Just t <- tails r = Req t (sp . k)
      where
        tails = tail >=> tail >=> tail >=> tail
        tail = either (\ _ -> Nothing) Just . decomp
    showNested sp m = showParen True <$> sp m

fromOpM :: Op_ r => Comp (Op t) r -> Comp t r
fromOpM =
  fromUnopM .
    fromArithBM .
    fromCmpBM .
    fromLogicBM

type BlockExt_ r = (Extend r, Block (Ext r))
    
parseBlocks
 :: BlockExt_ r => Parser (Stmt (Ext r)) -> Parser (r -> r)
parseBlocks ps = go id where
  go k = (do
    ext <- parseExtend
    b <- parseBlock ps
    go (\ r -> ext (k r) b))
    <|> return k

type BlockExt s t = Extend (Block s) <: t

showBlockExt
 :: Applicative m
 => (forall x . s x -> (x -> m ShowS) -> m ShowS)
 -> Extend (Block s) a -> (a -> m ShowS) -> m ShowS
showBlockExt ss = showExtend (\ r k -> r `showBlock` (`ss` k))

fromBlockExt
 :: (BlockExt_ r, Applicative m)
 => (forall x . s x -> (x -> m r) -> m (Stmt r))
 -> Extend (Block s) a -> (a -> m r) -> m r
fromBlockExt ks = fromExtend (\ r k -> r `fromBlock` (`ks` k))

type Lit_ r =
  ( Text_ r, Fractional r, IsString r, Extern_ r, Block_ r )

parseLit :: Lit_ r => Parser (Stmt r) -> Parser r
parseLit ps =
  parseText                     -- '"' ...
    <|> parseNumber             -- digit ...
    <|> (parseIdent <* spaces)  -- alpha ...
    <|> parseExtern             -- '@' ...
    <|> parseBlock ps           -- '{' ... 


-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type Expr_ r =
  ( ExprF_ r, Chain_ (Compound r), ExprF_ (Compound r)
  , Ext r ~ Ext (Compound r)
  )
type ExprF_ r = 
  ( Field_ r, Op_ r
  , Text_ r, Fractional r, IsString r, Extern_ r
  , Block_ r, Extend_ r, Block_ (Ext r)
  , Stmt r ~ Stmt (Ext r)
  )
  -- r, Compound r, Stmt r, Ext r

-- | Parse a chain of field accesses and extensions
parseExpr
 :: Expr_ r => Parser (Stmt r) -> Parser r
parseExpr ps = parseOp (term ps)
  where
    text, number, var, extern, block
      :: Expr_ r => Parser (Stmt r) -> Parser r
    text ps = 
      do
        t <- parseText
        f <- parseBlockExt
        (fieldNext a (f . fromText) ps
          <|> return (f (fromText t)))
    
    number ps =
      do
        n <- parseNumber
        f <- parseBlockExt
        (fieldNext n (f . fromNumber) ps
          <|> return (f (fromNumber n)))
    
    var ps =
      do
        i <- parseIdent 
        spaces
        f <- parseBlockExt
        (fieldNext a (f . fromString) ps
          <|> return (f (fromString i))
    
    litTerm :: Parser (Stmt r) -> Parser r
    litTerm pa runa ps =
      do
        a <- pa
        f <- parseBlockExt ps
        (fieldNext a (f . runa) ps
          <|> return (f (runa a))))
        <|> fieldNext (fromString "") ps
        
    
    blocksNext
     :: BlockExt_ r
     => Parser (Stmt (Ext r))
     -> Parser (r -> r)
    blocksNext ps = parseBlockExt ps
    
    fieldNext
     :: Field_ r
     => a -> (a -> Compond r) -> Parser (Stmt r) -> Parser r
    fieldNext a runa ps =
      do
        f <- parseField f
        g <- blocksNext ps
        (fieldNext a (g . runField . f) ps
          <|> return (g (runField (f a))))
    
    runField :: Field_ r => Field (Compound r) -> r
    runField = fromField id
    
    runBlockExt
     :: (Extend_ r, Block_ (Ext r))
     => Comp (Extend (Block (Const (Stmt r)))) r
     -> r
    runBlockExt =
      runIdentity
        (iter (fromBlockExt (const . pure . getConst)) pure)
    
        
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

type Expr s t =
  Field <:
    Text <:
    Number <:
    Var <:
    Extern <:
    Block s <:
    Extend (Block s) <:
    ArithB <:
    CmpB <:
    LogicB <:
    Unop <:
    t

showExprChainM
 :: (forall x. stmt x -> (x -> Comp t ShowS) -> Comp t ShowS)
 -> Comp (Expr s t) ShowS -> Comp t ShowS
showExprChainM ss =
  showOpM .
    showExtendM (\ r k -> r `showBlock` (`ss` k)) .
    showBlockM ss .
    showExternM .
    showVarM .
    showNumberM .
    showTextM .
    showChainM

fromExprChainM
 :: ( Lit_ r, Op_ r, Extend_ r, Block_ (Ext r)
    , Stmt r ~ Stmt (Ext r) Chain_ r
    )
 => (forall x. stmt x -> (x -> Comp t r) -> Comp t (Stmt r))
 -> Comp (Expr s t) r -> Comp t r
fromExprChainM ks =
  fromUnopM .
    fromLogicBM .
    fromCmpBM .
    fromArithBM .
    fromExtendM (\ r k -> r `fromBlock` (`ks` k)) .
    fromBlockM ks .
    fromExternM .
    fromVarM .
    fromNumberM .
    fromTextM .
    fromChainM
