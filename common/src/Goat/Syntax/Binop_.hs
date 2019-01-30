{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, ScopedTypeVariables, RankNTypes, DeriveFunctor #-}

module Goat.Syntax.Binop
  where

import Goat.Syntax.Symbol
import Goat.Syntax.Infix
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Data.Bifunctor

infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-
infix 4 #==, #!=, #<, #<=, #>, #>=, :#==, :#!=, :#<, :#<=, :#>, :#>=
infixr 3 #&&, :#&&
infixr 2 #||, :#||


-- Arithmetic operations
data AddOp a b =
    b :#+ a
  | b :#- a
  deriving (Eq, Show)
    
instance Bifunctor AddOp where
  bimap f g (b :#+ a) = g b :#+ f a
  bimap f g (b :#- a) = g b :#- f a
  
showAddOp :: (a -> ShowS) -> (b -> ShowS) -> AddOp a b -> ShowS
showAddOp f g (b :#+ a) = showInfix g f Add b a
showAddOp f g (b :#- a) = showInfix g f Sub b a

data MulOp a b =
    b :#* a
  | b :#/ a
  deriving (Eq, Show)

instance Bifunctor MulOp where
  bimap f g (b :#* a) = g b :#* f a
  bimap f g (b :#/ a) = g b :#/ f a

showMulOp :: (a -> ShowS) -> (b -> ShowS) -> MulOp a b -> ShowS
showMulOp f g (b :#* a) = showInfix g f Mul b a
showMulOp f g (b :#/ a) = showInfix g f Div b a

data PowOp a b =
    a :#^ b
  deriving (Eq, Show)
  
instance Bifunctor PowOp where
  bimap f g (a :#^ b) = f a :#^ g b
  
showPowOp :: (a -> ShowS) -> (b -> ShowS) -> PowOp a b -> ShowS
showPowOp f g (a :#^ b) = showInfix f g Pow a b

type ArithB =
  Expr (Assoc PowOp) (Expr (Assoc MulOp) (Assoc AddOp))

class ArithB_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
    
instance ArithB_ (Term a (ArithB a)) where
  a #+ b = liftOp (liftOp (infixlOp (:#+))) a b
  a #- b = liftOp (liftOp (infixlOp (:#-))) a b
  a #* b = liftOp (liftTerm (infixlOp (:#*))) a b
  a #/ b = liftOp (liftTerm (infixlOp (:#/))) a b
  a #^ b = liftTerm (infixrOp (:#^)) a b
  
showArithB
 :: (a -> ShowS) -> ArithB a -> ShowS
showArithB sa =
  showExpr
    (showAssoc showPowOp)
    (showExpr
      (showAssoc showMulOp)
      (showAssoc showAddOp))
    sa

-- | Parse an expression observing operator precedence
parseArithB :: ArithB_ r => Parser r -> Parser r
parseArithB p = parseAddB (parseMulB (parsePowB p)) where
  parseAddB p = Parsec.chainl1 p addOp where 
    addOp =
      (parseSymbol Add >> return (#+))
        <|> (parseSymbol Sub >> return (#-))
        
  parseMulB p = Parsec.chainl1 p mulOp where
    mulOp =
      (parseSymbol Mul >> return (#*))
        <|> (parseSymbol Div >> return (#/))
        
  parsePowB p = Parsec.chainr1 p powOp where
    powOp = parseSymbol Pow >> return (#^)
    
fromArithB
 :: ArithB_ r => (a -> r) -> ArithB a -> r
fromArithB ka =
  fromExpr 
    (fromAssoc fromPowOp)
    (fromExpr
      (fromAssoc fromMulOp)
      (fromAssoc fromAddOp))
    ka
  where
    fromAddOp
     :: ArithB_ r => (a -> r) -> (b -> r) -> AddOp a b -> r
    fromAddOp f g (b :#+ a) = g b #+ f a
    fromAddOp f g (b :#- a) = g b #- f a
    
    fromMulOp
     :: ArithB_ r => (a -> r) -> (b -> r) -> MulOp a b -> r
    fromMulOp f g (b :#* a) = g b #* f a
    fromMulOp f g (b :#/ a) = g b #/ f a
    
    fromPowOp
     :: ArithB_ r => (a -> r) -> (b -> r) -> PowOp a b -> r
    fromPowOp f g (a :#^ b) = f a #^ g b 


-- Comparison operations
data CmpOp a b =
    a :#== a
  | a :#!= a
  | a :#<  a
  | a :#<= a
  | a :#>  a
  | a :#>= a
  deriving (Eq, Show)

instance Bifunctor CmpOp where
  bimap f _ (a :#== b) = f a :#== f b
  bimap f _ (a :#!= b) = f a :#!= f b
  bimap f _ (a :#<  b) = f a :#<  f b
  bimap f _ (a :#<= b) = f a :#<= f b
  bimap f _ (a :#>  b) = f a :#>  f b
  bimap f _ (a :#>= b) = f a :#>= f b
  
showCmpOp
 :: (a -> ShowS) -> (b -> ShowS) -> CmpOp a b -> ShowS
showCmpOp f _ (a :#== b) = showInfix f f Eq a b
showCmpOp f _ (a :#!= b) = showInfix f f Ne a b
showCmpOp f _ (a :#<  b) = showInfix f f Lt a b
showCmpOp f _ (a :#<= b) = showInfix f f Le a b
showCmpOp f _ (a :#>  b) = showInfix f f Gt a b
showCmpOp f _ (a :#>= b) = showInfix f f Ge a b


type CmpB = Assoc CmpOp
  
class CmpB_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance CmpB_ (Term a (CmpB a)) where
  a #== b = infixOp (:#==) a b
  a #!= b = infixOp (:#!=) a b
  a #>  b = infixOp (:#>) a b
  a #>= b = infixOp (:#>=) a b
  a #<  b = infixOp (:#<) a b
  a #<= b = infixOp (:#<=) a b

showCmpB
 :: (a -> ShowS) -> CmpB a -> ShowS
showCmpB sa = showAssoc showCmpOp sa

parseCmpB :: CmpB_ r => Parser r -> Parser r
parseCmpB p =
  do
    a <- p
    (do
       s <- cmpOp
       b <- p
       return (s a b))
      <|> return a
  where
    cmpOp = 
      (parseSymbol Gt >> return (#>))
        <|> (parseSymbol Lt >> return (#<))
        <|> (parseSymbol Eq >> return (#==))
        <|> (parseSymbol Ne >> return (#!=))
        <|> (parseSymbol Ge >> return (#>=))
        <|> (parseSymbol Le >> return (#<=))
    
fromCmpB
 :: CmpB_ r => (a -> r) -> CmpB a -> r
fromCmpB ka = fromAssoc fromCmpOp ka
  where
    fromCmpOp
     :: CmpB_ r => (a -> r) -> (b -> r) -> CmpOp a b -> r
    fromCmpOp f _ (a :#== b) = f a #== f b
    fromCmpOp f _ (a :#!= b) = f a #!= f b
    fromCmpOp f _ (a :#>  b) = f a #>  f b
    fromCmpOp f _ (a :#>= b) = f a #>= f b
    fromCmpOp f _ (a :#<  b) = f a #<  f b
    fromCmpOp f _ (a :#<= b) = f a #<= f b


-- Logical operations
data AndOp a b = a :#&& b
  deriving (Eq, Show)

instance Bifunctor AndOp where
  bimap f g (a :#&& b) = f a :#&& g b

showAndOp :: (a -> ShowS) -> (b -> ShowS) -> AndOp a b -> ShowS
showAndOp f g (a :#&& b) = showInfix f g And a b

data OrOp a b = a :#|| b
  deriving (Eq, Show)

instance Bifunctor OrOp where
  bimap f g (a :#|| b) = f a :#|| g b

showOrOp :: (a -> ShowS) -> (b -> ShowS) -> OrOp a b -> ShowS
showOrOp f g (a :#|| b) = showInfix f g Or a b

type LogicB = Expr (Assoc AndOp) (Assoc OrOp)

class LogicB_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r
  
instance LogicB_ (Term a (LogicB a)) where
  a #|| b = liftOp (infixrOp (:#||)) a b
  a #&& b = liftTerm (infixrOp (:#&&)) a b
  
showLogicB
 :: (a -> ShowS) -> LogicB a -> ShowS
showLogicB sa =
  showExpr
    (showAssoc showAndOp)
    (showAssoc showOrOp)
    sa

parseLogicB :: LogicB_ r => Parser r -> Parser r
parseLogicB p = parseOrB (parseAndB p)
  where
    parseOrB p = Parsec.chainr1 p orOp where
      orOp = parseSymbol Or >> return (#||)
    
    parseAndB p = Parsec.chainr1 p andOp where
      andOp = parseSymbol And >> return (#&&)
      
fromLogicB
 :: LogicB_ r => (a -> r) -> LogicB a -> r
fromLogicB ka =
  fromExpr (fromAssoc fromAndOp) (fromAssoc fromOrOp) ka
  where
    fromOrOp f g (a :#|| b) = f a #|| g b
    fromAndOp f g (a :#&& b) = f a #&& g b

  
-- | Helper functions
showInfix
  :: (a -> ShowS) -> (b -> ShowS) -> Symbol -> a -> b -> ShowS
showInfix showa showb op a b =
  showa a
    . showChar ' '
    . showSymbol op
    . showChar ' '
    . showb b