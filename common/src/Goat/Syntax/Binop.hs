{-# LANGUAGE FlexibleInstances, DeriveFunctor #-}

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

data ArithOp a b =
    a :#+ b
  | a :#- b
  | a :#* b
  | a :#/ b
  | a :#^ b
  deriving (Eq, Show) 
  
showArithOp :: ArithOp ShowS ShowS -> ShowS
showArithOp (a :#+ b) = showInfix Add a b
showArithOp (a :#- b) = showInfix Sub a b
showArithOp (a :#* b) = showInfix Mul a b
showArithOp (a :#/ b) = showInfix Div a b
showArithOp (a :#^ b) = showInfix Pow a b

showParenArithOp :: (ArithOp a -> Bool) -> ArithOp a -> ShowS
showParenArithOp pred a = showParen (pred a) (showArithOp a)

showPrecLArithOp
 :: ArithOp (ArithOp ShowS ShowS) a
 -> ArithOp ShowS a
showPrecLArithOp = show'
  where
    show' (a :#+ b) = showAddL a :#+ b
    show' (a :#- b) = showAddL a :#- b
    show' (a :#* b) = showMulL a :#* b
    show' (a :#/ b) = showMulL a :#/ b
    show' (a :#^ b) = showPowL a :#^ b
    
    showAddL = showParenArithOp parenAddL
    showMulL = showParenArithOp parenMulL
    showPowL = showParenArithOp parenPowL
    
    parenAddL (_ :#+ _) = False
    parenAddL (_ :#- _) = False
    parenAddL (_ :#* _) = False
    parenAddL (_ :#/ _) = False
    parenAddL (_ :#^ _) = False
    
    parenMulL (_ :#+ _) = True
    parenMulL (_ :#- _) = True
    parenMulL (_ :#* _) = False
    parenMulL (_ :#/ _) = False
    parenMulL (_ :#^ _) = False
    
    parenPowL (_ :#+ _) = True
    parenPowL (_ :#- _) = True
    parenPowL (_ :#* _) = True
    parenPowL (_ :#/ _) = True
    parenPowL (_ :#^ _) = False

showPrecRArithOp :: ArithOp a (ArithOp ShowS ShowS) -> ArithOp a ShowS
showPrecRArithOp = show'
  where
    show' (a :#+ b) = a :#+ showAddR b
    show' (a :#- b) = a :#- showAddR b
    show' (a :#* b) = a :#* showMulR b
    show' (a :#/ b) = a :#/ showMulR b
    show' (a :#^ b) = a :#^ showPowR b
    
    showAddR = showParenArithOp parenAddR
    showMulR = showParenArithOp parenMulR
    showPowR = showParenArithOp parenPowR
    
    parenAddR (_ :#+ _) = True
    parenAddR (_ :#- _) = True
    parenAddR (_ :#* _) = False
    parenAddR (_ :#/ _) = False
    parenAddR (_ :#^ _) = False
    
    parenMulR (_ :#+ _) = True
    parenMulR (_ :#- _) = True
    parenMulR (_ :#* _) = True
    parenMulR (_ :#/ _) = True
    parenMulR (_ :#^ _) = False
    
    parenPowR (_ :#+ _) = True
    parenPowR (_ :#- _) = True
    parenPowR (_ :#* _) = True
    parenPowR (_ :#/ _) = True
    parenPowR (_ :#^ _) = True

showInfix
  :: Op -> ShowS -> ShowS -> ShowS
showInfix op sa sb =
  sa
    . showChar ' '
    . showOp op
    . showChar ' '
    . sb
  
  
data Arith a =
    ArithPure a
  | ArithOp (ArithOp (Arith a) (Arith a))
  deriving (Eq, Ord)

class Arith_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance Arith_ (Arith a) where
  (#+) = (:#+)
  (#-) = (:#-)
  (#*) = (:#*)
  (#/) = (:#/)
  (#^) = (:#^)
  
showsPrecArith
 :: forall a
  . (forall x . ArithOp a x -> ArithOp ShowS x)
 -> (forall x . ArithOp x a -> ArithOp x ShowS)
 -> ArithOp (Arith a) (Arith a)
 -> ArithOp ShowS ShowS
showsPrecArith spl spr = show'
  where
    show' = showr . showl
  
    showl :: ArithOp (Arith a) b -> ArithOp ShowS b
    showl = withArithOp (\ op a b -> showlWith (`op` b) a)
    
    showlWith
     :: (forall x . x -> ArithOp x a) -> Arith a -> ArithOp ShowS a
    showlWith ctr (ArithPure a) = spl (ctr a)
    showlWith ctr (ArithOp e) = showsPrecLArithOp (ctr (show' e))
    
    showr :: ArithOp a (Arith b) -> ArithOp a ShowS
    showr = withArithOp (\ op a b -> showrWith (a `op`) b)
    
    showrWith
     :: (forall x . x -> ArithOp a x) -> Arith a -> ArithOp a ShowS
    showrWith ctr (ArithPure b) = spr (ctr b)
    showrWith ctr (ArithOp e)   = showsPrecRArithOp (ctr (show' e))
    

withArithOp :: ((forall x y . x -> y -> ArithOp x y) -> c) -> ArithOp a b -> c
withArithOp op (a :#+ b) = op (:#+) a b
withArithOp op (a :#- b) = op (:#-) a b
withArithOp op (a :#* b) = op (:#*) a b
withArithOp op (a :#/ b) = op (:#/) a b
withArithOp op (a :#^ b) = op (:#^) a b
  
  
-- | Parse an expression observing operator precedence
parseArith :: Arith_ r => Parser r -> Parser r
parseArith p = parseAdd p where
  parseAdd p = Parsec.chainl1 (parseMul p) addOp where 
    addOp =
      (parseOp Add >> return (#+))
        <|> (parseOp Sub >> return (#-))
        
  parseMul p = Parsec.chainl1 (parsePow p) mulOp where
    mulOp =
      (parseOp Mul >> return (#*))
        <|> (parseOp Div >> return (#/))
        
  parsePow p = Parsec.chainl1 p powOp where
    powOp = parseOp Pow >> return (#^)

    
fromArith :: Arith_ r => Arith r -> r
fromArith (ArithPure r) = r
fromArith (ArithOp e) = case e of
  a :#+ b -> fromArithOp (#+) a b
  a :#- b -> fromArithOp (#-) a b
  a :#* b -> fromArithOp (#*) a b
  a :#/ b -> fromArithOp (#/) a b
  a :#^ b -> fromArithOp (#^) a b
  where
    fromArithOp
     :: Arith_ r => (r -> r -> r) -> Arith r -> Arith r -> r
    fromArithOp op a b = fromArith a `op` fromArith b
    
    
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

showParenCmpOp :: (CmpOp ShowS ShowS -> Bool) -> Cmp ShowS ShowS -> ShowS
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
  . (forall x . CmpOp x a -> CmpOp ShowS a)
 -> (forall x . CmpOp a x -> CmpOp a ShowS)
 -> CmpOp (Cmp a) (Cmp a)
 -> CmpOp ShowS ShowS
showsPrecCmp spl spr = show'
  where
    show' = showr . showl
  
    showl :: forall b . CmpOp (Cmp a) b -> CmpOp ShowS b
    showl = withCmpOp (\ op a b -> showlWith (`op` b) a)
    
    showlWith :: (forall x . x -> CmpOp x b) -> Cmp a -> CmpOp ShowS b
    showlWith ctr (CmpPure a) = spl (ctr a)
    showlWith ctr (CmpOp e) = ctr (showsPrecCmpOp (show' e))
    
    showr :: forall b . CmpOp b (Cmp a) -> CmpOp b ShowS
    showr = withCmpOp (\ op a b -> showrWith (a `op`) b)
    
    showrWith :: (forall x . x -> CmpOp a b) -> Cmp a -> CmpOp a ShowS
    showrWith ctr (CmpPure a) = spr (ctr a)
    showrWith ctr (CmpOp e) = ctr (showsPrecCmpOp (show' e))
    
    showsPrecCmpOp = showParenCmpOp (const True)


withCmpOp :: ((forall x y . x -> y -> CmpOp x y) -> c) -> CmpOp a b -> c
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
      (parseOp Gt >> return (#>))
        <|> (parseOp Lt >> return (#<))
        <|> (parseOp Eq >> return (#==))
        <|> (parseOp Ne >> return (#!=))
        <|> (parseOp Ge >> return (#>=))
        <|> (parseOp Le >> return (#<=))

    
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
