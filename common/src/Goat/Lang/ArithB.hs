{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Goat.Lang.ArithB
  where

import Goat.Comp
import Goat.Lang.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))
import Text.Parsec.Text (Parser)
import Control.Applicative (liftA2)
import Control.Monad (join)

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
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
showArithB :: (a -> ShowS) -> ArithB a -> ShowS
showArithB s (a :#+ b) = s a . showPad "+" . s b
showArithB s (a :#- b) = s a . showPad "-" . s b
showArithB s (a :#* b) = s a . showPad "*" . s b
showArithB s (a :#/ b) = s a . showPad "/" . s b
showArithB s (a :#^ b) = s a . showPad "^" . s b


fromArithB
 :: ArithB_ r => (a -> r) -> ArithB a -> r
fromArithB k (a :#+ b) = k a #+ k b
fromArithB k (a :#- b) = k a #- k b
fromArithB k (a :#* b) = k a #* k b
fromArithB k (a :#/ b) = k a #/ k b
fromArithB k (a :#^ b) = k a #^ k b 

instance Member ArithB ArithB where uprism = id
    
instance Member ArithB r => ArithB_ (Comp r a) where
  a #+ b = join (send (a :#+ b))
  a #- b = join (send (a :#- b))
  a #* b = join (send (a :#* b))
  a #/ b = join (send (a :#/ b))
  a #^ b = join (send (a :#^ b))


showPrecArithB
 :: ArithB (Either ShowS (ArithB ShowS))
 -> Either ShowS (ArithB ShowS)
showPrecArithB =
  showAdd (showMul (showPow (showNested showPrecArithB)))
  where
    showAdd, showMul, showPow, showNested
     :: (forall x . (ArithB ShowS -> x) ->
          ArithB  -> ArithB ShowS)
     -> (ArithB ShowS -> r)
     -> ArithB (Either a (ArithB a)) -> r
    showAdd sa s (a :#+ b) =
      either id s a :#+ either id (showAdd sa Left) (s b)
    showAdd sa s (a :#- b) =
      either id (sa Left) (s a) :#- either id (showAdd sa Left) (s b)
    showAdd sa s m = sa s m
    
    showMul sa s (a :#* b) =
      either id (sa Left) (s a) :#* either id (showMul sa Left) (s b)
    showMul sa s (a :#/ b) =
      either id (sa Left) (s a) :#/ either id (showMul sa Left) (s b)
    showMul sa s m = sa s m
    
    showPow sa s (a :#^ b) =
      either id (showPow sa Left) (s a) :#^ either id (sa Left) (s b)
    showPow sa s m = sa s m
    
    showNested sa s m = sa s m
  
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
      return (showArithB id (a :#+ b))
    showAdd' sa (Req (Head (a :#- b)) k) = do
      a <- sa (k a)
      b <- showAdd' sa (k b)
      return (showArithB id (a :#- b))
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


-- | helper functions
showPad s = showChar ' ' . showSymbol s . showChar ' '
