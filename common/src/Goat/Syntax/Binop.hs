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


newtype ArithBinop a =
  ArithBinop (BinopL AddOp (BinopL MulOp (BinopR PowOp a)))
  deriving (Eq, Show, Functor)
  
arithAdd
 :: ArithBinop a
 -> BinopL AddOp (BinopL MulOp (BinopR PowOp a))
arithAdd (ArithBinop a) = a

arithMul
 :: MonadFree ArithBinop m
 => ArithBinop (m a)
 -> BinopL MulOp (BinopR PowOp (m a))
arithMul (ArithBinop (LiftBL a)) = a
arithMul a                       = LiftBL (LiftBR (wrap a))

arithPow
 :: MonadFree ArithBinop m
 => ArithBinop (m a)
 -> BinopR PowOp (m a)
arithPow (ArithBinop (LiftBL (LiftBL a))) = a
arithPow a                                = LiftBR (wrap a)

arithF :: MonadFree ArithBinop m => ArithBinop (m a) -> m a
arithF (ArithBinop (LiftBL (LiftBL (LiftBR a)))) = a
arithF a                                       = wrap a

type ArithBin a = ArithBinop (F ArithBinop a)

class ArithBin_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance ArithBin_ (ArithBin a) where
  a #+ b = ArithBinop (BinopL (arithAdd a :#+ arithMul b))
  a #- b = ArithBinop (BinopL (arithAdd a :#- arithMul b))
  a #* b = ArithBinop (LiftBL (BinopL (arithMul a :#* arithPow b)))
  a #/ b = ArithBinop (LiftBL (BinopL (arithMul a :#/ arithPow b)))
  a #^ b = ArithBinop (LiftBL (LiftBL (BinopR (arithF a :#^ arithPow b))))
  
  
showArithBin
 :: (a -> ShowS) -> ArithBin a -> ShowS
showArithBin showa = showArithBinop (showF showa)
  where 
    showArithBinop :: (a -> ShowS) -> ArithBinop a -> ShowS
    showArithBinop showa (ArithBinop opl) =
      fromBinopL showAddOp (fromBinopL showMulOp (fromBinopR showPowOp showa)) opl
      
    showF showa (F f) = f showa (showParen True . showArithBinop id)

  
  
-- | Parse an expression observing operator precedence
parseArithBin :: ArithBin_ r => Parser r -> Parser r
parseArithBin p = parseAdd p where
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

    
fromArithBin :: ArithBin_ r => ArithBin r -> r
fromArithBin = fromArithBinop fromF
  where
    fromArithBinop
     :: ArithBin_ r => (a -> r) -> ArithBinop a -> r
    fromArithBinop f (ArithBinop opl) =
      fromBinopL fromAddOp (fromBinopL fromMulOp (fromBinopR fromPowOp f)) opl
    
    fromAddOp
     :: ArithBin_ r => (a -> r) -> (b -> r) -> AddOp a b -> r
    fromAddOp f g (a :#+ b) = f a #+ g b
    fromAddOp f g (a :#- b) = f a #- g b
    
    fromMulOp
     :: ArithBin_ r => (a -> r) -> (b -> r) -> MulOp a b -> r
    fromMulOp f g (a :#* b) = f a #* g b
    fromMulOp f g (a :#/ b) = f a #/ g b
    
    fromPowOp :: ArithBin_ r => (a -> r) -> (b -> r) -> PowOp a b -> r
    fromPowOp f g (a :#^ b) = f a #^ g b
    
    fromF :: ArithBin_ r => F ArithBinop r -> r
    fromF (F f) = f id (fromArithBinop id)
    
    
data CmpBinop a b =
    a :#== b
  | a :#!= b
  | a :#<  b
  | a :#<= b
  | a :#>  b
  | a :#>= b
  deriving (Eq, Show)
  
showCmpBinop
 :: (a -> ShowS) -> (b -> ShowS) -> CmpBinop a b -> ShowS
showCmpBinop f g (a :#== b) = showInfix f g Eq a b
showCmpBinop f g (a :#!= b) = showInfix f g Ne a b
showCmpBinop f g (a :#<  b) = showInfix f g Lt a b
showCmpBinop f g (a :#<= b) = showInfix f g Le a b
showCmpBinop f g (a :#>  b) = showInfix f g Gt a b
showCmpBinop f g (a :#>= b) = showInfix f g Ge a b

instance Bifunctor CmpBinop where
  bimap f g (a :#== b) = f a :#== g b
  bimap f g (a :#!= b) = f a :#!= g b
  bimap f g (a :#<  b) = f a :#<  g b
  bimap f g (a :#<= b) = f a :#<= g b
  bimap f g (a :#>  b) = f a :#>  g b
  bimap f g (a :#>= b) = f a :#>= g b

cmpF
 :: MonadFree (BinopA CmpBinop) m
 => BinopA CmpBinop (m a)
 -> m a
cmpF (LiftB a) = a
cmpF a         = wrap a

type CmpBin a = BinopA CmpBinop (F (BinopA CmpBinop) a)
  
class CmpBin_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance CmpBin_ (CmpBin a) where
  a #== b = BinopA (cmpF a :#== cmpF b)
  a #!= b = BinopA (cmpF a :#!= cmpF b)
  a #>  b = BinopA (cmpF a :#> cmpF b)
  a #>= b = BinopA (cmpF a :#>= cmpF b)
  a #<  b = BinopA (cmpF a :#<  cmpF b)
  a #<= b = BinopA (cmpF a :#<= cmpF b)

showCmpBin
 :: (a -> ShowS) -> CmpBin a -> ShowS
showCmpBin showa = fromBinopA showCmpBinop (showF showa)
  where
    showF showa (F f) =
      f showa (showParen True . fromBinopA showCmpBinop id)

parseCmpBin :: CmpBin_ r => Parser r -> Parser r
parseCmpBin p =
  do
    a <- p
    (do
       s <- cmpBinop
       b <- p
       return (s a b))
      <|> return a
  where
    cmpBinop = 
      (parseSymbol Gt >> return (#>))
        <|> (parseSymbol Lt >> return (#<))
        <|> (parseSymbol Eq >> return (#==))
        <|> (parseSymbol Ne >> return (#!=))
        <|> (parseSymbol Ge >> return (#>=))
        <|> (parseSymbol Le >> return (#<=))

    
fromCmpBin :: CmpBin_ r => CmpBin r -> r
fromCmpBin = fromBinopA fromCmpBinOp fromF
  where
    fromF (F f) = f id (fromBinopA fromCmpBinOp id)
    
    fromCmpBinOp
     :: CmpBin_ r => (a -> r) -> (b -> r) -> CmpBinop a b -> r
    fromCmpBinOp f g (a :#== b) = f a #== g b
    fromCmpBinOp f g (a :#!= b) = f a #!= g b
    fromCmpBinOp f g (a :#>  b) = f a #> g b
    fromCmpBinOp f g (a :#>= b) = f a #>= g b
    fromCmpBinOp f g (a :#<  b) = f a #< g b
    fromCmpBinOp f g (a :#<= b) = f a #<= g b
    
    
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

newtype LogicBinop a = LogicBinop (BinopR OrOp (BinopR AndOp a))
  deriving (Eq, Show, Functor)

logicOr
 :: LogicBinop a -> BinopR OrOp (BinopR AndOp a)
logicOr (LogicBinop a) = a

logicAnd
 :: MonadFree LogicBinop m
 => LogicBinop (m a)
 -> BinopR AndOp (m a)
logicAnd (LogicBinop (LiftBR a)) = a
logicAnd a                       = LiftBR (wrap a)

logicF
 :: MonadFree LogicBinop m => LogicBinop (m a) -> m a
logicF (LogicBinop (LiftBR (LiftBR a))) = a
logicF a                                = wrap a

type LogicBin a = LogicBinop (F LogicBinop a)

class LogicBin_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r
  
instance LogicBin_ (LogicBin r) where
  a #|| b = LogicBinop (BinopR (logicAnd a :#|| logicOr b))
  a #&& b = LogicBinop (LiftBR (BinopR (logicF a :#&& logicAnd b)))
  
showLogicBin :: (a -> ShowS) -> LogicBin a -> ShowS
showLogicBin showa = showLogicBinop (showF showa)
  where
    showLogicBinop :: (a -> ShowS) -> LogicBinop a -> ShowS
    showLogicBinop showa (LogicBinop opr) =
      fromBinopR showOrOp (fromBinopR showAndOp showa) opr
      
    showF :: (a -> ShowS) -> F LogicBinop a -> ShowS
    showF showa (F f) = f showa (showParen True . showLogicBinop id)

parseLogicBin :: LogicBin_ r => Parser r -> Parser r
parseLogicBin = parseOr
  where
    parseOr p = Parsec.chainr1 (parseAnd p) orOp where
      orOp = parseSymbol Or >> return (#||)
    
    parseAnd p = Parsec.chainr1 p andOp where
      andOp = parseSymbol And >> return (#&&)
      
fromLogicBin :: LogicBin_ r => LogicBin r -> r
fromLogicBin = fromLogicBinop fromF where
  fromLogicBinop :: LogicBin_ r => (a -> r) -> LogicBinop a -> r
  fromLogicBinop froma (LogicBinop opr) =
    fromBinopR fromOrOp (fromBinopR fromAndOp froma) opr
    
  fromOrOp f g (a :#|| b) = f a #|| g b
  fromAndOp f g (a :#&& b) = f a #&& g b
  fromF (F f) = f id (fromLogicBinop id)
