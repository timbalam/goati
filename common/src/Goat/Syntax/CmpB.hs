{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, RankNTypes, ScopedTypeVariables #-}
module Goat.Syntax.CmpB
  where

import Goat.Co
import Goat.Syntax.ArithB (layer, showPad)
import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
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

instance CmpB_ (Flip Comp a (CmpB <: t)) where
  a #== b = fsend (a :#== b)
  a #!= b = fsend (a :#!= b)
  a #>  b = fsend (a :#>  b)
  a #>= b = fsend (a :#>= b)
  a #<  b = fsend (a :#<  b)
  a #<= b = fsend (a :#<= b)

showCmpB
 :: forall t
      . (Comp t ShowS -> ShowS)
     -> Comp (CmpB <: t) ShowS -> ShowS
showCmpB st = st . showOp showCmp'
  where
    showOp
     :: ( forall x
            . CmpB x
           -> (x -> Comp (CmpB <: t) ShowS)
           -> Comp t ShowS
        )
     -> Comp (CmpB <: t) ShowS
     -> Comp t ShowS
    showOp = layer (showOp showCmp')

    showNested
      :: CmpB a
      -> (a -> Comp (CmpB <: t) ShowS)
      -> Comp t ShowS
    showNested h k = do
      a <- showCmp' h k
      return (showParen True a)
    
    showCmp'
     :: CmpB a -> (a -> Comp (CmpB <: t) ShowS)
     -> Comp t ShowS
    showCmp' h k =
      return (showCmpB' (st . showOp showNested . k) h)
    
    showCmpB'
      :: (a -> ShowS) -> CmpB a -> ShowS
    showCmpB' sa (a :#== b) = sa a . showPad "==" . sa b
    showCmpB' sa (a :#!= b) = sa a . showPad "!=" . sa b
    showCmpB' sa (a :#>  b) = sa a . showPad ">"  . sa b
    showCmpB' sa (a :#>= b) = sa a . showPad ">=" . sa b
    showCmpB' sa (a :#<  b) = sa a . showPad "<"  . sa b
    showCmpB' sa (a :#<= b) = sa a . showPad "<=" . sa b


fromCmpB
 :: CmpB_ r
 => (Comp t r -> r)
 -> Comp (CmpB <: t) r -> r
fromCmpB kt =
  kt
  . handle (\ h k -> return (fromCmpB' (kt . k) h))
  where
    fromCmpB' ka (a :#== b) = ka a #== ka b
    fromCmpB' ka (a :#!= b) = ka a #!= ka b
    fromCmpB' ka (a :#>  b) = ka a #>  ka b
    fromCmpB' ka (a :#>= b) = ka a #>= ka b
    fromCmpB' ka (a :#<  b) = ka a #<  ka b
    fromCmpB' ka (a :#<= b) = ka a #<= ka b
