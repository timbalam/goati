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
   
data OpL p a =
    LiftL a
  | OpL (p (OpL p a) a)

fromOpL
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> OpL p a -> r
fromOpL fromp froma (LiftL a) = froma a
fromOpL fromp froma (OpL p) = fromp (fromOpL fromp froma) froma p

instance (Eq a, Eq (p (OpL p a) a)) => Eq (OpL p a) where
  LiftL a == LiftL b = a == b
  OpL pa  == OpL pb  = pa == pb
  _       == _       = False
  
instance (Show a, Show (p (OpL p a) a)) => Show (OpL p a) where
  showsPrec i (LiftL a) = showParen (i>10) (showString "LiftL " . showsPrec 11 a)
  showsPrec i (OpL pa) = showParen (i>10) (showString "OpL " . showsPrec 11 pa)

instance Bifunctor p => Functor (OpL p) where
  fmap f (LiftL a) = LiftL (f a)
  fmap f (OpL p) = OpL (bimap (fmap f) f p)


data OpR p a =
    LiftR a
  | OpR (p a (OpR p a))
  
fromOpR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> OpR p a -> r
fromOpR fromp froma (LiftR a) = froma a
fromOpR fromp froma (OpR p) = fromp froma (fromOpR fromp froma) p

instance (Eq a, Eq (p a (OpR p a))) => Eq (OpR p a) where
  LiftR a == LiftR b = a == b
  OpR pa  == OpR pb  = pa == pb
  _       == _       = False
  
instance (Show a, Show (p a (OpR p a))) => Show (OpR p a) where
  showsPrec d (LiftR a) = showParen (d > 10) (showString "LiftR " . showsPrec 11 a)
  showsPrec d (OpR pa) = showParen (d > 10) (showString "OpR " . showsPrec 11 pa)

instance Bifunctor p => Functor (OpR p) where
  fmap f (LiftR a) = LiftR (f a)
  fmap f (OpR p) = OpR (bimap f (fmap f) p)


data OpA p a =
    LiftA a
  | OpA (p a a)
  
fromOpA
  :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
  -> (a -> r) -> OpA p a -> r
fromOpA fromp froma (LiftA a) = froma a
fromOpA fromp froma (OpA p) = fromp froma froma p

instance (Eq a, Eq (p a a)) => Eq (OpA p a) where
  LiftA a == LiftA b = a == b
  OpA pa  == OpA pb  = pa == pb
  _       == _       = False
  
instance (Show a, Show (p a a)) => Show (OpA p a) where
  showsPrec d (LiftA a) = showParen (d>10) (showString "LiftA " . showsPrec 11 a)
  showsPrec d (OpA a) = showParen (d>10) (showString "OpA " . showsPrec 11 a)

instance Bifunctor p => Functor (OpA p) where
  fmap f (LiftA a) = LiftA (f a)
  fmap f (OpA p) = OpA (bimap f f p)


newtype ArithOp a = ArithOp (OpL AddOp (OpL MulOp (OpR PowOp a)))
  deriving (Eq, Show, Functor)
  
arithAdd :: ArithOp a -> OpL AddOp (OpL MulOp (OpR PowOp a))
arithAdd (ArithOp a) = a

arithMul :: MonadFree ArithOp m => ArithOp (m a) -> OpL MulOp (OpR PowOp (m a))
arithMul (ArithOp (LiftL a)) = a
arithMul a                   = LiftL (LiftR (wrap a))

arithPow :: MonadFree ArithOp m => ArithOp (m a) -> OpR PowOp (m a)
arithPow (ArithOp (LiftL (LiftL a))) = a
arithPow a                           = LiftR (wrap a)

arithF :: MonadFree ArithOp m => ArithOp (m a) -> m a
arithF (ArithOp (LiftL (LiftL (LiftR a)))) = a
arithF a                                   = wrap a

type Arith a = ArithOp (F ArithOp a)

class Arith_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance Arith_ (Arith a) where
  a #+ b = ArithOp (OpL (arithAdd a :#+ arithMul b))
  a #- b = ArithOp (OpL (arithAdd a :#- arithMul b))
  a #* b = ArithOp (LiftL (OpL (arithMul a :#* arithPow b)))
  a #/ b = ArithOp (LiftL (OpL (arithMul a :#/ arithPow b)))
  a #^ b = ArithOp (LiftL (LiftL (OpR (arithF a :#^ arithPow b))))
  
  
showArith
 :: (a -> ShowS) -> Arith a -> ShowS
showArith showa = showArithOp (showF showa)
  where 
    showArithOp :: (a -> ShowS) -> ArithOp a -> ShowS
    showArithOp showa (ArithOp opl) =
      fromOpL showAddOp (fromOpL showMulOp (fromOpR showPowOp showa)) opl
      
    showF showa (F f) = f showa (showParen True . showArithOp id)

  
  
-- | Parse an expression observing operator precedence
parseArith :: Arith_ r => Parser r -> Parser r
parseArith p = parseAdd p where
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

    
fromArith :: Arith_ r => Arith r -> r
fromArith = fromArithOp fromF
  where
    fromArithOp :: Arith_ r => (a -> r) -> ArithOp a -> r
    fromArithOp f (ArithOp opl) =
      fromOpL fromAddOp (fromOpL fromMulOp (fromOpR fromPowOp f)) opl
    
    fromAddOp :: Arith_ r => (a -> r) -> (b -> r) -> AddOp a b -> r
    fromAddOp f g (a :#+ b) = f a #+ g b
    fromAddOp f g (a :#- b) = f a #- g b
    
    fromMulOp :: Arith_ r => (a -> r) -> (b -> r) -> MulOp a b -> r
    fromMulOp f g (a :#* b) = f a #* g b
    fromMulOp f g (a :#/ b) = f a #/ g b
    
    fromPowOp :: Arith_ r => (a -> r) -> (b -> r) -> PowOp a b -> r
    fromPowOp f g (a :#^ b) = f a #^ g b
    
    fromF :: Arith_ r => F ArithOp r -> r
    fromF (F f) = f id (fromArithOp id)
    
    
data CmpOp a b =
    a :#== b
  | a :#!= b
  | a :#<  b
  | a :#<= b
  | a :#>  b
  | a :#>= b
  deriving (Eq, Show)
  
showCmpOp :: (a -> ShowS) -> (b -> ShowS) -> CmpOp a b -> ShowS
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

cmpF :: MonadFree (OpA CmpOp) m => OpA CmpOp (m a) -> m a
cmpF (LiftA a) = a
cmpF a         = wrap a

type Cmp a = OpA CmpOp (F (OpA CmpOp) a)
  
class Cmp_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance Cmp_ (Cmp a) where
  a #== b = OpA (cmpF a :#== cmpF b)
  a #!= b = OpA (cmpF a :#!= cmpF b)
  a #>  b = OpA (cmpF a :#> cmpF b)
  a #>= b = OpA (cmpF a :#>= cmpF b)
  a #<  b = OpA (cmpF a :#<  cmpF b)
  a #<= b = OpA (cmpF a :#<= cmpF b)

showCmp
 :: (a -> ShowS) -> Cmp a -> ShowS
showCmp showa = fromOpA showCmpOp (showF showa)
  where
    showF showa (F f) = f showa (showParen True . fromOpA showCmpOp id)

parseCmp :: Cmp_ r => Parser r -> Parser r
parseCmp p =
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

    
fromCmp :: Cmp_ r => Cmp r -> r
fromCmp = fromOpA fromCmpOp fromF
  where
    fromF (F f) = f id (fromOpA fromCmpOp id)
    
    fromCmpOp :: Cmp_ r => (a -> r) -> (b -> r) -> CmpOp a b -> r
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

newtype LogicOp a = LogicOp (OpR OrOp (OpR AndOp a))
  deriving (Eq, Show, Functor)

logicOr
 :: LogicOp a -> OpR OrOp (OpR AndOp a)
logicOr (LogicOp a) = a

logicAnd
 :: MonadFree LogicOp m => LogicOp (m a) -> OpR AndOp (m a)
logicAnd (LogicOp (LiftR a)) = a
logicAnd a                   = LiftR (wrap a)

logicF
 :: MonadFree LogicOp m => LogicOp (m a) -> m a
logicF (LogicOp (LiftR (LiftR a))) = a
logicF a                           = wrap a

type Logic a = LogicOp (F LogicOp a)

class Logic_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r
  
instance Logic_ (Logic r) where
  a #|| b = LogicOp (OpR (logicAnd a :#|| logicOr b))
  a #&& b = LogicOp (LiftR (OpR (logicF a :#&& logicAnd b)))
  
showLogic :: (a -> ShowS) -> Logic a -> ShowS
showLogic showa = showLogicOp (showF showa)
  where
    showLogicOp :: (a -> ShowS) -> LogicOp a -> ShowS
    showLogicOp showa (LogicOp opr) =
      fromOpR showOrOp (fromOpR showAndOp showa) opr
      
    showF :: (a -> ShowS) -> F LogicOp a -> ShowS
    showF showa (F f) = f showa (showParen True . showLogicOp id)

parseLogic :: Logic_ r => Parser r -> Parser r
parseLogic = parseOr
  where
    parseOr p = Parsec.chainr1 (parseAnd p) orOp where
      orOp = parseSymbol Or >> return (#||)
    
    parseAnd p = Parsec.chainr1 p andOp where
      andOp = parseSymbol And >> return (#&&)
      
fromLogic :: Logic_ r => Logic r -> r
fromLogic = fromLogicOp fromF where
  fromLogicOp :: Logic_ r => (a -> r) -> LogicOp a -> r
  fromLogicOp froma (LogicOp opr) =
    fromOpR fromOrOp (fromOpR fromAndOp froma) opr
    
  fromOrOp f g (a :#|| b) = f a #|| g b
  fromAndOp f g (a :#&& b) = f a #&& g b
  fromF (F f) = f id (fromLogicOp id)
