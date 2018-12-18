{-# LANGUAGE FlexibleInstances, DeriveFunctor #-}

module Goat.Syntax.Binop
  where
  
import Goat.Syntax.Prec
import Goat.Syntax.Field (Puts)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Control.Monad.Free
  
infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-
infix 4 #==, #!=, #<, #<=, #>, #>=, :#==, :#!=, :#<, :#<=, :#>, :#>=

data Arith a = 
    a :#+ a
  | a :#- a
  | a :#* a
  | a :#/ a
  | a :#^ a
  deriving (Eq, Show, Functor)

class Arith_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance Arith_ (Free Arith a) where
  a #+ b = Free (a :#+ b)
  a #- b = Free (a :#- b)
  a #* b = Free (a :#* b)
  a #/ b = Free (a :#/ b)
  a #^ b = Free (a :#^ b)
  
  
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


showArith :: Puts a -> Puts (Arith a)
showArith showa pred aritha = case aritha of
  a :#+ b -> shows' Add a b
  a :#- b -> shows' Sub a b
  a :#* b -> shows' Mul a b
  a :#/ b -> shows' Div a b
  a :#^ b -> shows' Pow a b
  where
    shows' = showBinop showa pred


showBinop
  :: Puts a -> (Op -> Bool) -> Op -> a -> a -> ShowS
showBinop showa pred op a b =
  showParen (pred op) 
    (showa pred' a
      . showChar ' '
      . showOp op
      . showChar ' '
      . showa pred' b)
  where
    pred' = (`doesNotPreceed` op)
  
  
data Cmp a =
    a :#== a
  | a :#!= a
  | a :#<  a
  | a :#<= a
  | a :#>  a
  | a :#>= a
  deriving (Eq, Show, Functor)
  
class Cmp_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance Cmp_ (Free Cmp a) where
  a #== b = Free (a :#== b)
  a #!= b = Free (a :#!= b)
  a #>  b = Free (a :#>  b)
  a #>= b = Free (a :#>= b)
  a #<  b = Free (a :#<  b)
  a #<= b = Free (a :#<= b)
  
        
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


showCmp :: Puts a -> Puts (Cmp a)
showCmp showa pred cmpa = case cmpa of
  a :#== b -> shows' Eq a b
  a :#!= b -> shows' Ne a b
  a :#>  b -> shows' Gt a b
  a :#>= b -> shows' Ge a b
  a :#<  b -> shows' Lt a b
  a :#<= b -> shows' Le a b
  where
    shows' = showBinop showa pred
    
    

data Precedence =
    LeftAssoc
  | RightAssoc
  | NoAssoc

  
  
pointPrec :: a :#. b -> ShowS #. ShowS

-- | a `prec` b returns a 'Precedence' type deciding whether
-- operator a associates with unambiguously higher precedence than b.
prec :: Op -> Op -> Precedence
prec Point _     = LeftAssoc
prec _     Point = RightAssoc
prec Pow   Pow   = LeftAssoc
prec Pow   Mul   = LeftAssoc
prec Pow   Div   = LeftAssoc
prec Pow   Add   = LeftAssoc
prec Pow   Sub   = LeftAssoc
prec Mul   Pow   = RightAssoc
prec Div   Pow   = RightAssoc
prec Add   Pow   = RightAssoc
prec Sub   Pow   = RightAssoc
prec Mul   Mul   = LeftAssoc
prec Mul   Div   = LeftAssoc
prec Mul   Add   = LeftAssoc
prec Mul   Sub   = LeftAssoc
prec Div   Mul   = LeftAssoc
prec Div   Div   = LeftAssoc
prec Div   Add   = LeftAssoc
prec Div   Sub   = LeftAssoc
prec Add   Mul   = RightAssoc
prec Sub   Mul   = RightAssoc
prec Add   Div   = RightAssoc
prec Sub   Div   = RightAssoc
prec Add   Add   = LeftAssoc
prec Add   Sub   = LeftAssoc
prec Sub   Add   = LeftAssoc
prec Sub   Sub   = LeftAssoc
prec Not   _     = LeftAssoc
prec _     _     = NoAssoc


preceeds :: Op -> Op -> Bool
preceeds a b = case a `prec` b of 
  LeftAssoc -> True
  _         -> False

doesNotPreceed :: Op -> Op -> Bool
doesNotPreceed a b = not (preceeds a b)
 