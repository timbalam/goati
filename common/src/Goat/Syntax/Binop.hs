{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, RankNTypes, DeriveFunctor #-}

module Goat.Syntax.Binop
  where
  
import Goat.Syntax.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Control.Monad.Free
  
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
  
data MulOp a b =
    a :#* b
  | a :#/ b
  deriving (Eq, Show)
  
showMulOp :: (a -> ShowS) -> (b -> ShowS) -> ArithOp a b -> ShowS
showMulOp f g (a :#* b) = showInfix f g Mul a b
showMulOp f g (a :#/ b) = showInfix f g Div a b
  
data PowOp a b =
  a :#^ b
  deriving (Eq, Show) 
  
showPowOp :: (a -> ShowS) -> (b -> ShowS) -> ArithOp a b -> ShowS
showPowOp f g (a :#^ b) = showInfix f g Pow a b

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
  deriving (Eq, Show)

fromOpL
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> OpL p a -> r
fromOpL fromp froma (LiftL a) = froma a
fromOpL fromp froma (OpL p) = fromp (fromOpL fromp froma) froma p

        
data OpR p a =
    LiftR a
  | OpR (p a (OpR p a))
  deriving (Eq, Show)
  
fromOpR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> OpR p a -> r
fromOpR fromp froma (LiftR a) = froma a
fromOpR fromp froma (OpR p) = fromp froma (showOpR fromp froma) p


data OpA p a =
    LiftA
  | OpA (p a a)
  deriving (Eq, Show)
  
fromOpA
  :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
  -> (a -> r) -> OpA p a -> r
fromOpA fromp froma (LiftA a) = froma a
fromOpA fromp froma (OpA p) = fromp froma froma p


newtype ArithOp a = ArithOp (OpL AddOp (OpL MulOp (OpR PowOp a))) deriving (Eq, Show)

type Arith a = ArithOp (F ArithOp a)

class Arith_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance Arith_ (Arith a) where
  a #+ b = ArithOp (add a :#+ mul b)
  a #- b = ArithOp (add a :#- mul b)
  a #* b = ArithOp (LiftL (mul a :#* pow b))
  a #/ b = ArithOp (LiftL (mul a :#/ pow b))
  a #^ b = ArithOp (LiftL (LiftL (f a :#^ pow b)))
  
  add (ArithOp a) = a
  
  mul (ArithOp (LiftL a)) = a
  mul a                   = LiftL (LiftR (wrap a))
  
  pow (ArithOp (LiftL (LiftL a))) = a
  pow a                           = LiftR (wrap a)
  
  f (ArithOp (LiftL (LiftL (LiftR a)))) = a
  f a                                   = wrap a
  
  
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
    fromAddOp f g (a :#+ b) = f a #+ f b
    fromAddOp f g (a :#- b) = f a #- f b
    
    fromMulOp :: Arith_ r => (a -> r) -> (b -> r) -> MulOp a b -> r
    fromMulOp f g (a :#* b) = f a #* f b
    fromMulOp f g (a :#/ b) = f a #/ f b
    
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

type Cmp a = OpA CmpOp (F (OpA CmpOp) a)
  
class Cmp_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance Cmp_ (Cmp a) where
  a #== b = OpA (f a :#== f b)
  a #!= b = OpA (f a :#!= f b)
  a #>  b = OpA (f a :#> f b)
  a #>= b = OpA (f a :#>= f b)
  a #<  b = OpA (f a :#<  f b)
  a #<= b = OpA (f a :#<= f b)
  
  f (LiftA a) = a
  f a         = wrap a

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
    
    fromCmpOp :: Cmp_ r => CmpOp r -> r
    fromCmpOp (a :#== b) = a #== b
    fromCmpOp (a :#!= b) = a #!= b
    fromCmpOp (a :#>  b) = a #> b
    fromCmpOp (a :#>= b) = a #>= b
    fromCmpOp (a :#<  b) = a #< b
    fromCmpOp (a :#<= b) = a #<= b
    
    
data AndOp a b = a :#&& b deriving (Eq, Show)

showAndOp :: (a -> ShowS) -> (b -> ShowS) -> AndOp a b -> ShowS
showAndOp f g (a :#&& b) = showInfix f g And a b

data OrOp a b = a :#|| b deriving (Eq, Show)

showOrOp :: (a -> ShowS) -> (b -> ShowS) -> OrOp a b -> ShowS
showOrOp f g (a :#|| b) = showInfix f g Or a b

newtype LogicOp a = LogicOp (OpR OrOp (OpR AndOp a)) deriving (Eq, Show)

type Logic a = LogicOp (F LogicOp a)

class Logic_ r where
  (#&&) :: r -> r -> r
  (#||) :: r -> r -> r
  
instance Logic_ (Logic r) where
  a #|| b = LogicOp (or a :#|| and b)
  a #&& b = LogicOp (and a :#&& f b)
  
  or (LogicOp a) = a
  
  and (LogicOp (LiftR a)) = a
  and a                   = LiftR (wrap a)
  
  f (LogicOp (LiftR (LiftR a))) = a
  f a                           = wrap a
  
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
    parseOr p = P.chainr1 (parseAnd p) orOp where
      orOp = parseSymbol Or >> return (#||)
    
    parseAnd p = P.chainr1 p andOp where
      andOp = parseSymbol And >> return (#&&)
      
fromLogic :: Logic_ r => Logic r -> r
fromLogic = fromLogicOp fromF where
  fromLogicOp :: Logic_ r => LogicOp r -> r
  fromLogicOp (LogicOp opr) =
    fromOpR fromOrOp (fromOpR fromAndOp id) opr
    
  fromOrOp (a :#|| b) = a #|| b
  fromAndOp (a :#&& b) = a #&& b
  fromF (F f) = f id (fromLogicOp id)