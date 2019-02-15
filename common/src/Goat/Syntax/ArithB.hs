{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, FlexibleContexts #-}
module Goat.Syntax.ArithB
  where

import Goat.Co
import Goat.Syntax.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import Text.Parsec.Text (Parser)

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
    
instance ArithB_ (Flip Comp a (ArithB <: t)) where
  a #+ b = fsend (a :#+ b)
  a #- b = fsend (a :#- b)
  a #* b = fsend (a :#* b)
  a #/ b = fsend (a :#/ b)
  a #^ b = fsend (a :#^ b)
  
showArithB
 :: Comp (ArithB <: t) ShowS -> Comp t ShowS
showArithB = showOp showArith'
  where
    showOp
     :: ( forall x
            . ArithB x
           -> (x -> Comp (ArithB <: t) ShowS)
           -> Comp t ShowS
        )
     -> Comp (ArithB <: t) ShowS -> Comp t ShowS
    showOp = layer (showOp showArith')
    
    showArith'
      :: ArithB x
      -> (x -> Comp (ArithB <: t) ShowS)
      -> Comp t ShowS
    showArith' =
      showAdd' (showMul' (showPow' showNested))
    
    showNested h k = do
      a <- showArith' h k
      return (showParen True a)
    
    showAdd', showMul', showPow'
     :: ( forall x
            . ArithB x
           -> (x -> Comp (ArithB <: t) ShowS)
           -> Comp t ShowS
        )
     -> ArithB a
     -> (a -> Comp (ArithB <: t) ShowS)
     -> Comp t ShowS
    showAdd' sa (a :#+ b) k = do
      a <- showOp sa (k a)
      b <- showOp (showAdd' sa) (k b)
      return (showArithB' (a :#+ b))
    showAdd' sa (a :#- b) k = do
      a <- showOp sa (k a)
      b <- showOp (showAdd' sa) (k b)
      return (showArithB' (a :#- b))
    showAdd' sa h         k = sa h k
    
    showMul' sa (a :#* b) k = do
      a <- showOp sa (k a)
      b <- showOp (showMul' sa) (k b)
      return (showArithB' (a :#* b))
    showMul' sa (a :#/ b) k = do
      a <- showOp sa (k a) 
      b <- showOp (showMul' sa) (k b)
      return (showArithB' (a :#/ b))
    showMul' sa h         k = sa h k
    
    showPow' sa (a :#^ b) k = do
      a <- showOp (showPow' sa) (k a)
      b <- showOp sa (k b)
      return (showArithB' (a :#^ b))
    showPow' sa h         k = sa h k
    
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
layer
 :: (Comp (h <: t) a -> Comp t a)
 -> ( forall x
    . h x -> (x -> Comp (h <: t) a) -> Comp t a
    )
 -> Comp (h <: t) a -> Comp t a
layer f g (Done s) = Done s
layer f g (Req (Tail t) k) = Req t (f . k)
layer f g (Req (Head h) k) = g h k


showPad s = showChar ' ' . showSymbol s . showChar ' '
