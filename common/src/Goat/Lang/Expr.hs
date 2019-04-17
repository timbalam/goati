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
  showUnopM .
    showArithBM .
    showCmpBM .
    showLogicBM

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
 :: BlockExt_ r => Comp (BlockExt (Stmt (Ext r)) t) r -> Comp t r
fromBlockExt = fromExtendM (`fromBlock` pure)

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
 :: Lit_ r => Comp (Lit (Stmt r) t) r -> Comp t r
fromLit =
  fromBlockM pure .
    fromExternM .
    fromVarM .
    fromNumberM .
    fromTextM


-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
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

type Feat stmt t =
  Text <:
    Number <:
    Var <:
    Extern <:
    Block stmt <:
    Extend (Block stmt Void) <:
    t

fromFeat :: Feat_ r => Comp (Feat (Stmt r) t) r -> Comp t r
fromFeat =
  fromExtendM (`fromBlock` pure) . 
    fromBlockM pure .
    fromExternM .
    fromVarM .
    fromNumberM .
    fromTextM

type FieldExt_ r = (Field_ r, Extend_ r, Block_ (Ext r))

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
 => Comp (FieldExt (Compound r) (Stmt (Ext r)) t) r -> Comp t r
fromFieldExt =
  fromExtendM (`fromBlock` pure) . fromFieldM pure

type ChainExt_ r =
  ( FieldExt_ r, FieldExt_ (Compound r)
  , Chain_ (Compound r), Ext r ~ Ext (Compound r)
  )

-- | Parse a chain of field accesses and extensions
parseChainExt
 :: ChainExt_ r
 => Parser (Stmt (Ext r)) -> Parser (Compound r -> r)
parseChainExt ps = do
  f <- parseFieldExt ps
  (parseChainExt ps <&> \ g -> g . cloneFieldExt . f)
    <|> return (cloneFieldExt . f)
  where
    cloneFieldExt
      :: FieldExt_ r
      => Comp (FieldExt (Compound r) (Stmt (Ext r)) Null) Void -> r
    cloneFieldExt = handleAll fromFieldExt

type Term_ r =
  ( Field_ r, Feat_ r
  , Chain_ (Compound r), Feat_ (Compound r)
  , Ext r ~ Ext (Compound r)
  )

parseTerm
 :: Term_ r => Parser (Stmt r) -> Parser r
parseTerm ps =
  (do
    a <- parseFeat ps                 -- '"' ...
                                      -- digit ...
                                      -- alpha ...
                                      -- '@' ...
                                      -- '{' ...
    (do 
      f <- parseChainExt ps
      return (f (cloneFeat a))) <|>
        return (cloneFeat a)) <|>
    (do 
      f <- parseChainExt ps
      return (f (fromString "")))     -- '.' ...
  where
    cloneFeat
     :: Feat_ r
     => Comp (Feat (Stmt (Ext r)) Null) Void -> r
    cloneFeat = handleAll fromFeat
