{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, FlexibleContexts #-}
module Goat.Syntax.ArithB
  where

import Goat.Co
import Goat.Syntax.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import Text.Parsec.Text (Parser)
import Control.Applicative (liftA2)

infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-

-- Arithmetic operations
class ArithB_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r

-- | Observe operator precedence
parseArithB :: ArithB_ r => Parser r -> Parser r
parseArithB p =
  parseAddB (parseMulB (parsePowB p))
  where
    parseAddB p = Parsec.chainl1 p addOp
    parseMulB p = Parsec.chainl1 p mulOp
    parsePowB p = Parsec.chainr1 p powOp
    
    addOp =
      (parseSymbol "+" >> return (#+))
        <|> (parseSymbol "-" >> return (#-))
    mulOp =
      (parseSymbol "*" >> return (#*))
        <|> (parseSymbol "/" >> return (#/))
    powOp = parseSymbol "^" >> return (#^)

data ArithB a =
    a :#+ a
  | a :#- a
  | a :#* a
  | a :#/ a
  | a :#^ a
  deriving (Eq, Show)
    
instance ArithB_ (SComp (ArithB <: t)) where
  a #+ b = ssend (a :#+ b)
  a #- b = ssend (a :#- b)
  a #* b = ssend (a :#* b)
  a #/ b = ssend (a :#/ b)
  a #^ b = ssend (a :#^ b)
  
showArithB
 :: Comp (ArithB <: t) ShowS -> Comp t ShowS
showArithB = showAdd' (showMul' (showPow' (showNested showArithB)))
  where
    showNested, showAdd', showMul', showPow'
     :: (Comp (ArithB <: t) ShowS -> Comp t ShowS)
     -> Comp (ArithB <: t) ShowS -> Comp t ShowS
    showNested sa (Done s)         = Done s
    showNested sa (Req (Tail t) k) = 
      Req t (showNested sa . k) 
    showNested sa m                = do
      a <- sa m
      return (showParen True a)
    
    showAdd' sa (Req (Head (a :#+ b)) k) = do
      a <- sa (k a)
      b <- showAdd' sa (k b)
      return (showArithB' (a :#+ b))
    showAdd' sa (Req (Head (a :#- b)) k) = do
      a <- sa (k a)
      b <- showAdd' sa (k b)
      return (showArithB' (a :#- b))
    showAdd' sa m                        = sa m
    
    showMul' sa (Req (Head (a :#* b)) k) = do
      a <- sa (k a)
      b <- showMul' sa (k b)
      return (showArithB' (a :#* b))
    showMul' sa (Req (Head (a :#/ b)) k) = do
      a <- sa (k a) 
      b <- showMul' sa (k b)
      return (showArithB' (a :#/ b))
    showMul' sa m                        = sa m
    
    showPow' sa (Req (Head (a :#^ b)) k) = do
      a <- showPow' sa (k a)
      b <- sa (k b)
      return (showArithB' (a :#^ b))
    showPow' sa m                        = sa m
    
    showArithB' :: ArithB ShowS -> ShowS
    showArithB' (a :#+ b) = a . showPad "+" . b
    showArithB' (a :#- b) = a . showPad "-" . b
    showArithB' (a :#* b) = a . showPad "*" . b
    showArithB' (a :#/ b) = a . showPad "/" . b
    showArithB' (a :#^ b) = a . showPad "^" . b


fromArithB
 :: ArithB_ r
 => Comp (ArithB <: t) r -> Comp t r
fromArithB = handle fromArithB'
  where
    fromArithB' (a :#+ b) k = liftA2 (#+) (k a) (k b)
    fromArithB' (a :#- b) k = liftA2 (#-) (k a) (k b)
    fromArithB' (a :#* b) k = liftA2 (#*) (k a) (k b)
    fromArithB' (a :#/ b) k = liftA2 (#/) (k a) (k b)
    fromArithB' (a :#^ b) k = liftA2 (#^) (k a) (k b) 


-- | helper functions
showPad s = showChar ' ' . showSymbol s . showChar ' '
