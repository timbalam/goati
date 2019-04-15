{-# LANGUAGE RankNTypes, TypeOperators, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Goat.Lang.ArithB
  where

import Goat.Comp
import Goat.Lang.Symbol
import Goat.Util ((<&>))
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
  deriving (Eq, Show)
  
showArithB
 :: Applicative m => ArithB a -> (a -> m ShowS) -> m ShowS
showArithB (a :#+ b) s = liftA2 (showPad "+") (s a) (s b)
showArithB (a :#- b) s = liftA2 (showPad "-") (s a) (s b)
showArithB (a :#* b) s = liftA2 (showPad "*") (s a) (s b)
showArithB (a :#/ b) s = liftA2 (showPad "/") (s a) (s b)
showArithB (a :#^ b) s = liftA2 (showPad "^") (s a) (s b)

fromArithB
 :: (Applicative m, ArithB_ r) => ArithB a -> (a -> m r) -> m r
fromArithB (a :#+ b) k = liftA2 (#+) (k a) (k b)
fromArithB (a :#- b) k = liftA2 (#-) (k a) (k b)
fromArithB (a :#* b) k = liftA2 (#*) (k a) (k b)
fromArithB (a :#/ b) k = liftA2 (#/) (k a) (k b)
fromArithB (a :#^ b) k = liftA2 (#^) (k a) (k b) 

instance Member ArithB ArithB where uprism = id
    
instance Member ArithB r => ArithB_ (Comp r a) where
  a #+ b = join (send (a :#+ b))
  a #- b = join (send (a :#- b))
  a #* b = join (send (a :#* b))
  a #/ b = join (send (a :#/ b))
  a #^ b = join (send (a :#^ b))
