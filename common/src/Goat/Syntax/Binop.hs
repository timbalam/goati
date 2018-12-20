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

fromOpL
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> OpL p a -> r
fromOpL fromp froma (LiftL a) = froma a
fromOpL fromp froma (OpL p) = fromp (fromOpL fromp froma) froma p

        
data OpR p a =
    LiftR a
  | OpR (p a (OpR p a))
  
fromOpR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> OpR p a -> r
fromOpR fromp froma (LiftR a) = froma a
fromOpR fromp froma (OpR p) = fromp froma (showOpR fromp froma) p
    
data Arith a =
  ArithOp (OpL AddOp (OpL MulOp (OpR PowOp (Either a (Arith a)))))

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
  a #^ b = ArithOp (LiftL (LiftL (eit a :#^ pow b)))
  
  add (ArithOp a) = a
  
  mul (ArithOp (LiftL a)) = a
  mul a                   = LiftL (LiftR (Right a))
  
  pow (ArithOp (LiftL (LiftL a))) = a
  pow a                           = LiftR (Right a)
  
  eit (ArithOp (LiftL (LiftL (LiftR a)))) = a
  eit a                                   = Right a
  
  
showArith
 :: forall a . (a -> ShowS) -> Arith a -> ShowS
showArith showa (ArithOp opl) =
  fromOpL showAddOp (fromOpL showMulOp (fromOpR showPowOp showEit)) opl
  where 
    showEit = either showa (showParen True . showArith showa)

  
  
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
        
  parsePow p = Parsec.chainl1 p powOp where
    powOp = parseSymbol Pow >> return (#^)

    
fromArith :: Arith_ r => Arith r -> r
fromArith (ArithOp opl) =
  fromOpL fromAddOp (fromOpL fromMulOp (fromOpR fromPowOp fromEit)) opl
  where
    fromAddOp :: Arith_ r => (a -> r) -> (b -> r) -> AddOp a b -> r
    fromAddOp f g (a :#+ b) = f a #+ f b
    fromAddOp f g (a :#- b) = f a #- f b
    
    fromMulOp :: Arith_ r => (a -> r) -> (b -> r) -> MulOp a b -> r
    fromMulOp f g (a :#* b) = f a #* f b
    fromMulOp f g (a :#/ b) = f a #/ f b
    
    fromPowOp :: Arith_ r => (a -> r) -> (b -> r) -> PowOp a b -> r
    fromPowOp f g (a :#^ b) = f a #^ g b
    
    fromEit :: Arith_ r => Either r (Arith r) -> r
    fromEit = either id fromArith
    
    
data CmpOp a b =
    a :#== b
  | a :#!= b
  | a :#<  b
  | a :#<= b
  | a :#>  b
  | a :#>= b
  deriving (Eq, Show)
  
showCmpOp :: CmpOp ShowS ShowS -> ShowS
showCmpOp (a :#== b) = showInfix Eq a b
showCmpOp (a :#!= b) = showInfix Ne a b
showCmpOp (a :#<  b) = showInfix Lt a b
showCmpOp (a :#<= b) = showInfix Le a b
showCmpOp (a :#>  b) = showInfix Gt a b
showCmpOp (a :#>= b) = showInfix Ge a b

showParenCmpOp :: (CmpOp ShowS ShowS -> Bool) -> CmpOp ShowS ShowS -> ShowS
showParenCmpOp pred a = showParen (pred a) (showCmpOp a)

data Cmp a =
    CmpPure a
  | CmpOp (CmpOp (Cmp a) (Cmp a))
  deriving (Eq, Show)
  
class Cmp_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance Cmp_ (Cmp a) where
  a #== b = CmpOp (a :#== b)
  a #!= b = CmpOp (a :#!= b)
  a #>  b = CmpOp (a :#>  b)
  a #>= b = CmpOp (a :#>= b)
  a #<  b = CmpOp (a :#<  b)
  a #<= b = CmpOp (a :#<= b)


showsPrecCmp
 :: forall a
  . (forall x . CmpOp a x -> CmpOp ShowS x)
 -> (forall x . CmpOp x a -> CmpOp x ShowS)
 -> CmpOp (Cmp a) (Cmp a)
 -> CmpOp ShowS ShowS
showsPrecCmp spl spr = show'
  where
    show' = showr . showl
  
    showl :: forall x . CmpOp (Cmp a) x -> CmpOp ShowS x
    showl = withCmpOp (\ op a b -> showlWith (`op` b) a)
    
    showlWith :: forall y . (forall x . x -> CmpOp x y) -> Cmp a -> CmpOp ShowS y
    showlWith ctr (CmpPure a) = spl (ctr a)
    showlWith ctr (CmpOp e) = ctr (showsPrecCmpOp (show' e))
    
    showr :: forall x . CmpOp x (Cmp a) -> CmpOp x ShowS
    showr = withCmpOp (\ op a b -> showrWith (a `op`) b)
    
    showrWith :: forall x . (forall y . y -> CmpOp x y) -> Cmp a -> CmpOp x ShowS
    showrWith ctr (CmpPure a) = spr (ctr a)
    showrWith ctr (CmpOp e) = ctr (showsPrecCmpOp (show' e))
    
    showsPrecCmpOp = showParenCmpOp (const True)


withCmpOp :: ((forall x y . x -> y -> CmpOp x y) -> a -> b -> c) -> CmpOp a b -> c
withCmpOp op (a :#== b) = op (:#==) a b
withCmpOp op (a :#!= b) = op (:#!=) a b
withCmpOp op (a :#>  b) = op (:#>) a b
withCmpOp op (a :#>= b) = op (:#>=) a b
withCmpOp op (a :#<  b) = op (:#<) a b
withCmpOp op (a :#<= b) = op (:#<=) a b


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
fromCmp (CmpPure r) = r
fromCmp (CmpOp e) = case e of 
  a :#== b -> fromCmpOp (#==) a b
  a :#!= b -> fromCmpOp (#!=) a b
  a :#>  b -> fromCmpOp (#>) a b
  a :#>= b -> fromCmpOp (#>=) a b
  a :#<  b -> fromCmpOp (#<) a b
  a :#<= b -> fromCmpOp (#<=) a b
  where
    fromCmpOp :: Cmp_ r => (r -> r -> r) -> Cmp r -> Cmp r -> r
    fromCmpOp op a b = fromCmp a `op` fromCmp b
