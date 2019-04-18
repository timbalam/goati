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


type FieldExt_ r =
  ( Field_ r, FieldChain_ (Compound r)
  , Extend_ r, ExtendChain_ (Ext r)
  , Extension (Ext r) ~ Extension r
  , Field_ (Ext r), Compound (Ext r) ~ Compound r
  , Extend_ (Compound r)
  , Extension (Compound r) ~ Extension r
  , Ext (Compound r) ~ Ext r
  )

parseFieldExt
 :: FieldExt_ r
 => Parser (Extension r) -> Parser (Compound r -> r)
parseFieldExt px = do
  f <- parsePath
  (do 
    g <- parseExtField px
    return (g . cloneField . f)) <|>
    return (cloneField . f)

parseExtField
 :: FieldExt_ r
 => Parser (Extension r) -> Parser (Ext r -> r)
parseExtField px = do
  f <- parseExtensions px
  (do
    g <- parseFieldExt px
    return (g . cloneExtend  . f)) <|>
    return (cloneExtend  . f)


-- | Expression with operator precedence
type Op_ r =
  (LogicB_ r, ArithB_ r, CmpB_ r, Unop_ r)

parseOp :: Op_ r => Parser r -> Parser r
parseOp p =
  parseLogicB (parseCmpB (parseArithB (parseUnop <*> p)))
  
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

type Expr_ r = (Op_ r, Op_ (Compound r), Op_ (Ext r))
  
parseExpr
 :: Expr_ r => Parser r -> Parser r
parseExpr p =
  parseLogicB
    (parseCmpB
      (parseArithB
        (parseUnop <*> parseTerm (p <|> parens (parseOp p)))))
  where
    parseTerm :: Expr_ r => Parser r -> Parser r
    term p = do
      a <- p
  where
    parens :: Parser a -> Parser a
    parens =
      Parsec.between
        (Parsec.char '(' >> spaces)
        (Parsec.char ')' >> spaces)

    
type Feat_ r =
  ( Op_ r, FieldExt_ r
  , Block_ (Extension r), Stmt (Extension r) ~ Stmt r
  )

type Feat c e s t =
  Op (Lit s (Field c <: Extend e (Block s Void) <: t))

fromFeatM
 :: Feat_ r
 => Comp (Feat (Compound r) (Ext r) (Stmt r) t) r -> Comp t r
fromFeatM =
  fromExtend pure (fromBlock pure) .
    fromField pure .
    fromLitM . 
    fromOpM



-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type Expr_ r =
  (Feat_ r, Feat_ (Compound r), Feat_ (Ext r))

parseExpr :: Term_ r => Parser (Stmt r) -> Parser r
parseExpr ps = 
  (do
    term <- parseLit ps <|> parseOp (parseExpr ps)
    (parseFieldExt ps <*> pure (cloneLit a)) <|>
      (parseExtField ps <*> pure (cloneLit a)) <|>
      return (cloneLit a)) <|>
    (fromSelf <$> parseSelf <**> parseFieldExt)
  where
    cloneFeat
     :: Feat_ r
     => Comp (Feat (Compound r) (Ext r) (Stmt r) Null) Void -> r
    cloneFeat = handleAll fromFeatM

  