{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Goat.Syntax.CmpB
  where

import Goat.Co
import Goat.Syntax.ArithB
import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Control.Applicative (liftA2)
import Control.Monad (join)
import Data.String (fromString)

-- Comparison operations
class CmpB_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r

parseCmpB :: CmpB_ r => Parser r -> Parser r
parseCmpB p =
  do
    a <- p
    (do
       s <- cmpOp
       b <- p
       return (s a b))
      <|> return a
  where
    cmpOp = 
      (parseSymbol ">" >> return (#>))
        <|> (parseSymbol "<" >> return (#<))
        <|> (parseSymbol "==" >> return (#==))
        <|> (parseSymbol "!=" >> return (#!=))
        <|> (parseSymbol ">=" >> return (#>=))
        <|> (parseSymbol "<=" >> return (#<=))

data CmpB a =
    a :#== a
  | a :#!= a
  | a :#<  a
  | a :#<= a
  | a :#>  a
  | a :#>= a
  deriving (Eq, Show)

instance CmpB_ (Comp (CmpB <: t) a) where
  a #== b = send (a :#== b)
  a #!= b = send (a :#!= b)
  a #>  b = send (a :#>  b)
  a #>= b = send (a :#>= b)
  a #<  b = send (a :#<  b)
  a #<= b = send (a :#<= b)

instance
  CmpB_ (Comp t (Comp (ArithB <: t) a))
   => CmpB_ (Comp (ArithB <: t) a) where
  a #== b = injop (#==) a b
  a #!= b = injop (#!=) a b
  a #>  b = injop (#>) a b
  a #>= b = injop (#>=) a b
  a #<  b = injop (#<) a b
  a #<= b = injop (#<=) a b
  
injop
 :: (Comp t (Comp (h <: t) a)
     -> Comp t (Comp (h <: t) a)
     -> Comp t (Comp (h <: t) a)) 
 -> Comp (h <: t) a -> Comp (h <: t) a -> Comp (h <: t) a
injop op a b =
  join (inj (return a `op` return b))

showCmpB
 :: Comp (CmpB <: t) ShowS -> Comp t ShowS
showCmpB = showCmp' (showNested showCmpB)
  where
    showNested, showCmp'
      :: (Comp (CmpB <: t) ShowS -> Comp t ShowS)
      -> Comp (CmpB <: t) ShowS -> Comp t ShowS
    showNested sa (Done s)         = Done s
    showNested sa (Req (Tail t) k) = Req t (showNested sa . k)
    showNested sa m                = do
      a <- sa m
      return (showParen True a)
    
    showCmp' sa (Req (Head h) k) = case h of
      a :#== b -> hdl (:#==) a b
      a :#!= b -> hdl (:#!=) a b
      a :#>  b -> hdl (:#>) a b
      a :#>= b -> hdl (:#>=) a b
      a :#<  b -> hdl (:#<) a b
      a :#<= b -> hdl (:#<=) a b
      where
        hdl op a b = do 
          a <- sa (k a)
          b <- sa (k b)
          return (showCmpB' (a `op` b))
    showCmp' sa m                 = sa m
    
    showCmpB'
      :: CmpB ShowS -> ShowS
    showCmpB' (a :#== b) = a . showPad "==" . b
    showCmpB' (a :#!= b) = a . showPad "!=" . b
    showCmpB' (a :#>  b) = a . showPad ">"  . b
    showCmpB' (a :#>= b) = a . showPad ">=" . b
    showCmpB' (a :#<  b) = a . showPad "<"  . b
    showCmpB' (a :#<= b) = a . showPad "<=" . b


fromCmpB
 :: CmpB_ r
 => Comp (CmpB <: t) r -> Comp t r
fromCmpB = handle fromCmpB'
  where
    fromCmpB' (a :#== b) k = liftA2 (#==) (k a) (k b)
    fromCmpB' (a :#!= b) k = liftA2 (#!=) (k a) (k b)
    fromCmpB' (a :#>  b) k = liftA2 (#>)  (k a) (k b)
    fromCmpB' (a :#>= b) k = liftA2 (#>=) (k a) (k b)
    fromCmpB' (a :#<  b) k = liftA2 (#<)  (k a) (k b)
    fromCmpB' (a :#<= b) k = liftA2 (#<=) (k a) (k b)
