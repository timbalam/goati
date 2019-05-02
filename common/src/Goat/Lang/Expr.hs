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
import Control.Applicative ((<**>))
import Control.Monad ((>=>))
import Data.Functor (($>))
import Data.Void (Void)
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

type Lit s t = Text <: Number <: Var <: Extern <: Block s <: t

fromLitM
 :: Lit_ r => Comp (Lit (Stmt r) t) r -> Comp t r
fromLitM =
  fromBlockM pure .
    fromExternM .
    fromVarM .
    fromNumberM .
    fromTextM

type FieldExtend_ r = (Field_ r, Extend_ r)

type FieldExtendChain_ c e x =
  ( Field_ c, Extend_ c, Field_ e, Extend_ e
  , Compound c ~ c, Ext c ~ e, Extension c ~ x
  , Compound e ~ c, Ext e ~ e, Extension e ~ x
  )

parseFieldNext
 :: (FieldExtend_ r, FieldExtendChain_ (Compound r) (Ext r) (Extension r))
 => Parser (Extension r) -> Parser (Compound r -> r)
parseFieldNext px = do
  f <- parseFieldLink
  (do 
    g <- parseExtendNext px
    return (g . cloneField . f)) <|>
    return (cloneField . f)

parseExtendNext
 :: (FieldExtend_ r, FieldExtendChain_ (Compound r) (Ext r) (Extension r))
 => Parser (Extension r) -> Parser (Ext r -> r)
parseExtendNext px = do
  f <- parseExtendLink px
  (do
    g <- parseFieldNext px
    return (g . cloneExtend  . f)) <|>
    return (cloneExtend  . f)

type FieldExtend c e x t = Field c <: Extend e x <: t

fromFieldExtendM
 :: FieldExtend_ r
 => Comp (FieldExtend (Compound r) (Ext r) (Extension r) t) r
 -> Comp t r
fromFieldExtendM = fromExtendM pure pure . fromFieldM pure

-- | Expression with operator precedence
type Op_ r =
  (LogicB_ r, ArithB_ r, CmpB_ r, Unop_ r)
  
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


-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type Expr_ r = (Op_ r, FieldExtend_ r, Lit_ r)
type ExprChain_ c e x s =
  ( FieldExtendChain_ c e x, Expr_ c, Expr_ e, Block_ x
  , Stmt c ~ s, Stmt e ~ s, Stmt x ~ s
  )
  
parseExpr
 :: (Expr_ r, ExprChain_ (Compound r) (Ext r) (Extension r) (Stmt r))
 => Parser (Stmt r) -> Parser r
parseExpr ps =
  parseLogicB
    (parseCmpB
      (parseArithB
        (parseUnop <*> term ps)))
  where
    term
     :: (Expr_ r, ExprChain_ (Compound r) (Ext r) (Extension r) (Stmt r))
     => Parser (Stmt r) -> Parser r
    term ps =
      (do
        a <- parseLit ps <|> parens (parseExpr ps)
        fieldNext (cloneExpr a) ps <|>
          extendNext (cloneExpr a) ps <|>
          return (cloneExpr a)) <|>
        (do
          s <- parseSelf
          fieldNext (fromSelf s) ps)
    
    fieldNext
     :: ( FieldExtend_ r
        , FieldExtendChain_ (Compound r) (Ext r) (Extension r)
        , Block_ (Extension r)
        )  
     => Compound r -> Parser (Stmt (Extension r)) -> Parser r
    fieldNext c ps = do
      f <- parseFieldNext (parseBlock ps)
      return (f c)
    
    extendNext
     :: ( FieldExtend_ r
        , FieldExtendChain_ (Compound r) (Ext r) (Extension r)
        , Block_ (Extension r)
        )
     => Ext r -> Parser (Stmt (Extension r)) -> Parser r
    extendNext e ps = do
      f <- parseExtendNext (parseBlock ps)
      return (f e)
    
    parens :: Parser a -> Parser a
    parens =
      Parsec.between
        (Parsec.char '(' >> spaces)
        (Parsec.char ')' >> spaces)

cloneExpr
 :: Expr_ r
 => Comp (Expr (Compound r) (Ext r) (Extension r) (Stmt r) Null) Void -> r
cloneExpr = handleAll fromExprM


type Expr c e x s t = Op (Field c <: Extend e x <: Lit s t)

fromExprM 
 :: Expr_ r
 => Comp (Expr (Compound r) (Ext r) (Extension r) (Stmt r) t) r -> Comp t r
fromExprM =
  fromLitM .
  fromExtendM pure pure .
  fromFieldM pure .
  fromOpM

type SomeExpr c e x s = Comp (Expr c e x s Null) Void
