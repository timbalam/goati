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
import Goat.Util ((<&>))
import Control.Applicative (Const(..))
import Control.Monad ((>=>))
import Data.Functor (($>))
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
 :: Comp (Op t) ShowS -> Comp t ShowS
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

type BlockExt_ r = (Extend_ r, Block_ (Ext r))
    
parseBlockExt
 :: BlockExt_ r => Parser (Stmt (Ext r)) -> Parser (r -> r)
parseBlockExt ps = go id where
  go k = (do
    ext <- parseExtend
    b <- parseBlock ps
    go (\ r -> ext (k r) b))
    <|> return k

type BlockExt s t = Extend (Block s Void) <: t

fromBlockExt
 :: (Applicative m, BlockExt_ r) 
 -> Comp (BlockExt (Stmt r) t) r -> Comp t r
fromBlockExt = fromExtend (fromBlock pure)

-- | Proof that 'BlockExt_ (Comp (BlockExt s Null) a)' instances exist with 'Stmt (Comp (BlockExt s Null) a) ~ s'
blockExtProof
 :: Comp (BlockExt s Null) a
 -> Comp (BlockExt s Null) b
 -> Comp (BlockExt s Null) b
blockExtProof = cloneBlockExt

type Lit_ r =
  ( Text_ r, Fractional r, IsString r, Extern_ r, Block_ r )

parseLit :: Lit_ r => Parser (Stmt r) -> Parser r
parseLit ps =
  parseText                     -- '"' ...
    <|> parseNumber             -- digit ...
    <|> (parseIdent <* spaces)  -- alpha ...
    <|> parseExtern             -- '@' ...
    <|> parseBlock ps           -- '{' ...

type Lit s t = Text <: Number <: Var <: Extern <: Block s <: t

fromLit
 :: Lit_ r => Comp (Lit (Stmt r) <: t) r -> Comp t r
fromLit =
  fromTextM .
    fromNumberM .
    fromVarM .
    fromExternM .
    fromBlockM pure


-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type Expr_ r =
  ( Field_ r, Feat_ r
  , Chain_ (Compound r), Feat_ (Compound r)
  , Ext r ~ Ext (Compound r)
  )

type Feat_ r = 
  ( Text_ r, Fractional r, IsString r, Extern_ r
  , Block_ r, Extend_ r, Block_ (Ext r)
  , Stmt r ~ Stmt (Ext r)
  )
  
parseFeat
 :: Feat_ r => Parser (Stmt r) -> Parser r
parseFeat ps = do
  a <- parseLit ps
  f <- parseBlockExt ps
  return (f a)

type Feat stmt =
  Text <:
    Number <:
    Var <:
    Extern <:
    Block stmt <:
    Extend (Block stmt Void) <:
    t

fromFeat :: Feat_ r => Comp (Feat (Stmt r) <: t) r -> Comp t r
fromFeat =
  fromTextM .
    fromNumberM .
    fromVarM .
    fromExternM .
    fromBlockM pure .
    fromExtendM (fromBlock pure)
  
type FieldExt_ = (Field_ r, Extend_ r, Block_ (Ext r))

parseFieldExt
 :: FieldExt_ r
 => Parser (Stmt (Ext r)) -> Parser (Compound r -> r)
parseFieldExt ps = do
  f <- parseField
  g <- parseBlockExt ps
  return (g . f)

type FieldExt cmp stmt t = Field cmp <: Extend (Block stmt Void) <: t

fromFieldExt
 :: FieldExt_ r
 => Comp (FieldExt (Compound r) (Stmt r) <: t) r -> Comp t r
fromFieldExt =
  fromFieldM pure . fromExtendM (fromBlock pure)

-- | Parse a chain of field accesses and extensions
parseExpr
 :: Expr_ r => Parser (Stmt r) -> Parser r
parseExpr ps = parseOp (termFirst ps)
  where
    termFirst
      :: Expr_ r => Parser (Stmt r) -> Parser r
    termFirst ps =
      (do
        a <- parseFeat ps                 -- '"' ...
                                          -- digit ...
                                          -- alpha ...
                                          -- '@' ...
                                          -- '{' ...
        fieldsNext (cloneFeat a) ps <|>
          return (cloneFeat a)) <|>
        fieldsNext (fromString "") ps     -- '.' ...
    
    cloneFeat
     :: Feat_ r => Block (Feat Null) Void -> r
    cloneBlock = handleAll fromFeat
    
    fieldsNext
     :: FieldExt_ r => Compound r -> Parser (Stmt r) -> Parser r
    fieldsNext c ps =
      do
        f <- parseFieldExt ps
        (fieldsNext (cloneFieldExt (f c)) ps
          <|> return (cloneFieldExt (f c)))
    
    cloneFieldExt
      :: FieldExt_ r
      => Comp (FieldExt (Compound r) (Stmt r) Null) Void -> r
    cloneFieldExt = handleAll fromFieldExt
