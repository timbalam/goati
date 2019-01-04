{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, ScopedTypeVariables, RankNTypes, DeriveFunctor #-}

module Goat.Syntax.Binop
  where
  
import Goat.Syntax.Symbol
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
    a :#+ b
  | a :#- b
  deriving (Eq, Show)
  
showAddOp :: (a -> ShowS) -> (b -> ShowS) -> AddOp a b -> ShowS
showAddOp f g (a :#+ b) = showInfix f g Add a b
showAddOp f g (a :#- b) = showInfix f g Sub a b

instance Bifunctor AddOp where
  bimap f g (a :#+ b) = f a :#+ g b
  bimap f g (a :#- b) = f a :#- g b
  
data MulOp a b =
    a :#* b
  | a :#/ b
  deriving (Eq, Show)
  
showMulOp :: (a -> ShowS) -> (b -> ShowS) -> MulOp a b -> ShowS
showMulOp f g (a :#* b) = showInfix f g Mul a b
showMulOp f g (a :#/ b) = showInfix f g Div a b

instance Bifunctor MulOp where
  bimap f g (a :#* b) = f a :#* g b
  bimap f g (a :#/ b) = f a :#/ g b
  
data PowOp a b =
  a :#^ b
  deriving (Eq, Show) 
  
showPowOp :: (a -> ShowS) -> (b -> ShowS) -> PowOp a b -> ShowS
showPowOp f g (a :#^ b) = showInfix f g Pow a b

instance Bifunctor PowOp where
  bimap f g (a :#^ b) = f a :#^ g b

showInfix
  :: (a -> ShowS) -> (b -> ShowS) -> Symbol -> a -> b -> ShowS
showInfix showa showb op a b =
  showa a
    . showChar ' '
    . showSymbol op
    . showChar ' '
    . showb b
   
data BinopL p a =
    LiftBL a
  | BinopL (p (BinopL p a) a)

fromBinopL
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> BinopL p a -> r
fromBinopL fromp froma (LiftBL a) = froma a
fromBinopL fromp froma (BinopL p) =
  fromp (fromBinopL fromp froma) froma p

instance (Eq a, Eq (p (BinopL p a) a)) => Eq (BinopL p a) where
  LiftBL a  == LiftBL b  = a == b
  BinopL pa == BinopL pb = pa == pb
  _         == _         = False
  
instance (Show a, Show (p (BinopL p a) a)) => Show (BinopL p a) where
  showsPrec i (LiftBL a) = showParen (i>10)
    (showString "LiftBL " . showsPrec 11 a)
  showsPrec i (BinopL pa) = showParen (i>10)
    (showString "BinopL " . showsPrec 11 pa)

instance Bifunctor p => Functor (BinopL p) where
  fmap f (LiftBL a) = LiftBL (f a)
  fmap f (BinopL p) = BinopL (bimap (fmap f) f p)


data BinopR p a =
    LiftBR a
  | BinopR (p a (BinopR p a))
  
fromBinopR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> BinopR p a -> r
fromBinopR fromp froma (LiftBR a) = froma a
fromBinopR fromp froma (BinopR p) =
  fromp froma (fromBinopR fromp froma) p

instance (Eq a, Eq (p a (BinopR p a))) => Eq (BinopR p a) where
  LiftBR a  == LiftBR b  = a == b
  BinopR pa == BinopR pb = pa == pb
  _         == _         = False
  
instance (Show a, Show (p a (BinopR p a))) => Show (BinopR p a) where
  showsPrec d (LiftBR a) = showParen (d > 10)
    (showString "LiftBR " . showsPrec 11 a)
  showsPrec d (BinopR pa) = showParen (d > 10)
    (showString "BinopR " . showsPrec 11 pa)

instance Bifunctor p => Functor (BinopR p) where
  fmap f (LiftBR a) = LiftBR (f a)
  fmap f (BinopR p) = BinopR (bimap f (fmap f) p)


data BinopA p a =
    LiftB a
  | BinopA (p a a)
  
fromBinopA
  :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
  -> (a -> r) -> BinopA p a -> r
fromBinopA fromp froma (LiftB a) = froma a
fromBinopA fromp froma (BinopA p) = fromp froma froma p

instance (Eq a, Eq (p a a)) => Eq (BinopA p a) where
  LiftB a   == LiftB b   = a == b
  BinopA pa == BinopA pb = pa == pb
  _         == _         = False
  
instance (Show a, Show (p a a)) => Show (BinopA p a) where
  showsPrec d (LiftB a) = showParen (d>10) (showString "LiftB " . showsPrec 11 a)
  showsPrec d (BinopA a) = showParen (d>10) (showString "BinopA " . showsPrec 11 a)

instance Bifunctor p => Functor (BinopA p) where
  fmap f (LiftB a) = LiftB (f a)
  fmap f (BinopA p) = BinopA (bimap f f p)


newtype ArithB a =
  ArithB (BinopL AddOp (BinopL MulOp (BinopR PowOp a)))
  deriving (Eq, Show, Functor)
  
arithAdd
 :: ArithB a
 -> BinopL AddOp (BinopL MulOp (BinopR PowOp a))
arithAdd (ArithB a) = a

arithMul
 :: MonadFree ArithB m
 => ArithB (m a)
 -> BinopL MulOp (BinopR PowOp (m a))
arithMul (ArithB (LiftBL a)) = a
arithMul a                   = LiftBL (LiftBR (wrap a))

arithPow
 :: MonadFree ArithB m
 => ArithB (m a)
 -> BinopR PowOp (m a)
arithPow (ArithB (LiftBL (LiftBL a))) = a
arithPow a                            = LiftBR (wrap a)

arithF :: MonadFree ArithB m => ArithB (m a) -> m a
arithF (ArithB (LiftBL (LiftBL (LiftBR a)))) = a
arithF a                                     = wrap a


class ArithB_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance MonadFree ArithB m => ArithB_ (ArithB (m a)) where
  a #+ b = ArithB (BinopL (arithAdd a :#+ arithMul b))
  a #- b = ArithB (BinopL (arithAdd a :#- arithMul b))
  a #* b = ArithB (LiftBL (BinopL (arithMul a :#* arithPow b)))
  a #/ b = ArithB (LiftBL (BinopL (arithMul a :#/ arithPow b)))
  a #^ b = ArithB (LiftBL (LiftBL (BinopR (arithF a :#^ arithPow b))))
  
  
showArithB
 :: (a -> ShowS) -> ArithB (F ArithB a) -> ShowS
showArithB showa = showArithB' (\ f -> 
  runF f showa (showParen True . showArithB' id))
  where 
    showArithB' :: (a -> ShowS) -> ArithB a -> ShowS
    showArithB' showa (ArithB opl) =
      fromBinopL showAddOp (fromBinopL showMulOp (fromBinopR showPowOp showa)) opl

  
  
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

    
fromArithB :: ArithB_ r => ArithB (F ArithB r) -> r
fromArithB = fromArithB' (iter (fromArithB' id))
  where
    fromArithB'
     :: ArithB_ r => (a -> r) -> ArithB a -> r
    fromArithB' f (ArithB opl) =
      fromBinopL fromAddOp (fromBinopL fromMulOp (fromBinopR fromPowOp f)) opl
    
    fromAddOp
     :: ArithB_ r => (a -> r) -> (b -> r) -> AddOp a b -> r
    fromAddOp f g (a :#+ b) = f a #+ g b
    fromAddOp f g (a :#- b) = f a #- g b
    
    fromMulOp
     :: ArithB_ r => (a -> r) -> (b -> r) -> MulOp a b -> r
    fromMulOp f g (a :#* b) = f a #* g b
    fromMulOp f g (a :#/ b) = f a #/ g b
    
    fromPowOp :: ArithB_ r => (a -> r) -> (b -> r) -> PowOp a b -> r
    fromPowOp f g (a :#^ b) = f a #^ g b
    
    
data CmpOp a b =
    a :#== b
  | a :#!= b
  | a :#<  b
  | a :#<= b
  | a :#>  b
  | a :#>= b
  deriving (Eq, Show)
  
showCmpOp
 :: (a -> ShowS) -> (b -> ShowS) -> CmpOp a b -> ShowS
showCmpOp f g (a :#== b) = showInfix f g Eq a b
showCmpOp f g (a :#!= b) = showInfix f g Ne a b
showCmpOp f g (a :#<  b) = showInfix f g Lt a b
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


type CmpB = BinopA CmpOp
  
cmpF
 :: MonadFree CmpB m
 => CmpB (m a)
 -> m a
cmpF (LiftB a) = a
cmpF a         = wrap a
  
class CmpB_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance MonadFree CmpB m => CmpB_ (CmpB (m a)) where
  a #== b = BinopA (cmpF a :#== cmpF b)
  a #!= b = BinopA (cmpF a :#!= cmpF b)
  a #>  b = BinopA (cmpF a :#> cmpF b)
  a #>= b = BinopA (cmpF a :#>= cmpF b)
  a #<  b = BinopA (cmpF a :#<  cmpF b)
  a #<= b = BinopA (cmpF a :#<= cmpF b)

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

newtype LogicB a = LogicB (BinopR OrOp (BinopR AndOp a))
  deriving (Eq, Show, Functor)

logicOr :: LogicB a -> BinopR OrOp (BinopR AndOp a)
logicOr (LogicB a) = a

logicAnd
 :: MonadFree LogicB m
 => LogicB (m a)
 -> BinopR AndOp (m a)
logicAnd (LogicB (LiftBR a)) = a
logicAnd a                   = LiftBR (wrap a)

logicF
 :: MonadFree LogicB m => LogicB (m a) -> m a
logicF (LogicB (LiftBR (LiftBR a))) = a
logicF a                            = wrap a

class LogicB_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r
  
instance MonadFree LogicB m => LogicB_ (LogicB (m a)) where
  a #|| b = LogicB (BinopR (logicAnd a :#|| logicOr b))
  a #&& b = LogicB (LiftBR (BinopR (logicF a :#&& logicAnd b)))
  
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
