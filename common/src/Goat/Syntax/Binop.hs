{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, ScopedTypeVariables, RankNTypes, DeriveFunctor #-}

module Goat.Syntax.Binop
  where
  
import Goat.Syntax.Symbol
import Goat.Syntax.Fixity
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Data.Bifunctor
import Control.Monad.Free.Church
  
infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-
infix 4 #==, #!=, #<, #<=, #>, #>=, :#==, :#!=, :#<, :#<=, :#>, :#>=
infixr 3 #&&, :#&&
infixr 2 #||, :#||

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
  
type AddB = Exp (ExpA AddOp)

showAddB = showExp (showExpA showAddOp)

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
  
type MulB = Exp (ExpA MulOp)

showMulB = showExp (showExpA showMulOp)
  
data PowOp a b =
    a :#^ b
  deriving (Eq, Show)
  
instance Bifunctor PowOp where
  bimap f g (a :#^ b) = f a :#^ g b
  
showPowOp :: (a -> ShowS) -> (b -> ShowS) -> PowOp a b -> ShowS
showPowOp f g (a :#^ b) = showInfix f g Pow a b

type PowB = Exp (ExpA PowB)

showPowB = showExp (showExpA showPowOp)


type ArithB f = AddB (MulB (PowB f))

class ArithB_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
    
instance ArithB_ (ArithB f a) where
  a #+ b = infixExp (:#+) a b
  a #- b = infixExp (:#-) a b
  a #* b = wrap a :#* wrap b
  a #/ b = wrap a :#/ wrap b
  a #^ b = wrap a :#^ wrap b
  
showArithB :: (a -> ShowS) -> ArithB a -> ShowS
showArithB
  
-- | Parse an expression observing operator precedence
parseArithB :: ArithB_ r => Parser r -> Parser r
parseArithB p = parseAdd p where
  parseAdd p = Parsec.chainl1 (parseMul p) addOp where 
    addOp =
      (parseSymbol Add >> return (#+))
        <|> (parseSymbol Sub >> return (#-))
        
  parseMul p = Parsec.chainl1 (parsePow p) mulOp where
    mulOp =
      (parseSymbol Mul >> return (#*))
        <|> (parseSymbol Div >> return (#/))
        
  parsePow p = Parsec.chainr1 p powOp where
    powOp = parseSymbol Pow >> return (#^)
    
fromArithB :: ArithB_ r => ArithB r -> r
fromArithB (ArithB a) = fromArithOp id id a
  where
    fromArithOp :: ArithB_ r => (a -> r) -> (b -> r) -> ArithOp a b -> r
    fromArithOp f g (b :#+ a) = g b #+ f a
    fromArithOp f g (b :#- a) = g b #- f a
    fromArithOp f g (b :#* a) = g b #* f a
    fromArithOp f g (b :#/ a) = g b #/ f a
    fromArithOp f g (a :#^ b) = f a #^ g b 


data CmpB a =
    a :#== a
  | a :#!= a
  | a :#<  a
  | a :#<= a
  | a :#>  a
  | a :#>= a
  deriving (Eq, Show)
  
showCmpB
 :: (a -> ShowS) -> CmpOp a -> ShowS
showCmpOp f (a :#== b) = showInfix f g Eq a b
showCmpOp f (a :#!= b) = showInfix f g Ne a b
showCmpOp f (a :#<  b) = showInfix f g Lt a b
showCmpOp f g (a :#<= b) = showInfix f g Le a b
showCmpOp f g (a :#>  b) = showInfix f g Gt a b
showCmpOp f g (a :#>= b) = showInfix f g Ge a b

instance Bifunctor CmpOp where
  bimap f g (a :#== b) = f a :#== g b
  bimap f g (a :#!= b) = f a :#!= g b
  bimap f g (a :#<  b) = f a :#<  g b
  bimap f g (a :#<= b) = f a :#<= g b
  bimap f g (a :#>  b) = f a :#>  g b
  bimap f g (a :#>= b) = f a :#>= g b


type CmpB = Infix CmpOp
  
cmpTerm
 :: MonadFree CmpB m
 => CmpB (m a)
 -> m a
cmpTerm (TermI a) = a
cmpTerm a         = wrap a
  
class CmpB_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance MonadFree CmpB m => CmpB_ (CmpB (m a)) where
  a #== b = Infix (cmpTerm a :#== cmpTerm b)
  a #!= b = Infix (cmpTerm a :#!= cmpTerm b)
  a #>  b = Infix (cmpTerm a :#>  cmpTerm b)
  a #>= b = Infix (cmpTerm a :#>= cmpTerm b)
  a #<  b = Infix (cmpTerm a :#<  cmpTerm b)
  a #<= b = Infix (cmpTerm a :#<= cmpTerm b)

showCmpB
 :: (a -> ShowS) -> CmpB (F CmpB a) -> ShowS
showCmpB showa = fromBinopA showCmpOp (\ (F f) ->
  f showa (showParen True . fromBinopA showCmpOp id))
  
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

    
fromCmpB :: CmpB_ r => CmpB (F CmpB r) -> r
fromCmpB = fromBinopA fromCmpOp (iter (fromBinopA fromCmpOp id))
  where
    fromCmpOp
     :: CmpB_ r => (a -> r) -> (b -> r) -> CmpOp a b -> r
    fromCmpOp f g (a :#== b) = f a #== g b
    fromCmpOp f g (a :#!= b) = f a #!= g b
    fromCmpOp f g (a :#>  b) = f a #> g b
    fromCmpOp f g (a :#>= b) = f a #>= g b
    fromCmpOp f g (a :#<  b) = f a #< g b
    fromCmpOp f g (a :#<= b) = f a #<= g b
   
    
    
data AndOp a b = a :#&& b
  deriving (Eq, Show)

showAndOp :: (a -> ShowS) -> (b -> ShowS) -> AndOp a b -> ShowS
showAndOp f g (a :#&& b) = showInfix f g And a b

instance Bifunctor AndOp where
  bimap f g (a :#&& b) = f a :#&& g b

data OrOp a b = a :#|| b
  deriving (Eq, Show)

showOrOp :: (a -> ShowS) -> (b -> ShowS) -> OrOp a b -> ShowS
showOrOp f g (a :#|| b) = showInfix f g Or a b

instance Bifunctor OrOp where
  bimap f g (a :#|| b) = f a :#|| g b

newtype LogicB a = LogicB (InfixR OrOp (InfixR AndOp a))
  deriving (Eq, Show, Functor)

logicOr :: LogicB a -> InfixR OrOp (InfixR AndOp a)
logicOr (LogicB a) = a

logicAnd
 :: MonadFree LogicB m
 => LogicB (m a)
 -> InfixR AndOp (m a)
logicAnd (LogicB (TermIR a)) = a
logicAnd a                   = TermIR (wrap a)

logicTerm
 :: MonadFree LogicB m => LogicB (m a) -> m a
logicTerm (LogicB (TermIR (TermIR a))) = a
logicTerm a                            = wrap a

class LogicB_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r
  
instance MonadFree LogicB m => LogicB_ (LogicB (m a)) where
  a #|| b = LogicB (InfixR (logicAnd a :#|| logicOr b))
  a #&& b = LogicB (TermIR (InfixR (logicTerm a :#&& logicAnd b)))
  
showLogicB :: (a -> ShowS) -> LogicB (F LogicB a) -> ShowS
showLogicB showa = showLogicB' (\ (F f) -> 
  f showa (showParen True . showLogicB' id))
  where
    showLogicB' :: (a -> ShowS) -> LogicB a -> ShowS
    showLogicB' showa (LogicB opr) =
      fromBinopR showOrOp (fromBinopR showAndOp showa) opr

parseLogicB :: LogicB_ r => Parser r -> Parser r
parseLogicB = parseOr
  where
    parseOr p = Parsec.chainr1 (parseAnd p) orOp where
      orOp = parseSymbol Or >> return (#||)
    
    parseAnd p = Parsec.chainr1 p andOp where
      andOp = parseSymbol And >> return (#&&)
      
fromLogicB :: LogicB_ r => LogicB (F LogicB r) -> r
fromLogicB = fromLogicB' (iter (fromLogicB' id)) where
  fromLogicB' :: LogicB_ r => (a -> r) -> LogicB a -> r
  fromLogicB' froma (LogicB opr) =
    fromBinopR fromOrOp (fromBinopR fromAndOp froma) opr
  
  fromOrOp f g (a :#|| b) = f a #|| g b
  fromAndOp f g (a :#&& b) = f a #&& g b
  
  

showInfix
  :: (a -> ShowS) -> (b -> ShowS) -> Symbol -> a -> b -> ShowS
showInfix showa showb op a b =
  showa a
    . showChar ' '
    . showSymbol op
    . showChar ' '
    . showb b
  
