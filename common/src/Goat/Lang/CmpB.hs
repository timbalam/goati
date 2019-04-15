{-# LANGUAGE TypeOperators, FlexibleContexts, FlexibleInstances, RankNTypes, ScopedTypeVariables, MultiParamTypeClasses #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.CmpB
  where

import Goat.Comp
import Goat.Lang.Symbol
import Goat.Util ((<&>))
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
 
showCmpB
 :: Applicative m => CmpB a -> (a -> m ShowS) -> m ShowS
showCmpB (a :#== b) s = liftA2 (showPad "==") (s a) (s b)
showCmpB (a :#!= b) s = liftA2 (showPad "!=") (s a) (s b)
showCmpB (a :#>  b) s = liftA2 (showPad ">")  (s a) (s b)
showCmpB (a :#>= b) s = liftA2 (showPad ">=") (s a) (s b)
showCmpB (a :#<  b) s = liftA2 (showPad "<")  (s a) (s b)
showCmpB (a :#<= b) s = liftA2 (showPad "<=") (s a) (s b)
  
fromCmpB
 :: (Applicative m, CmpB_ r) => CmpB a -> (a -> m r) -> m r
fromCmpB (a :#== b) k = liftA2 (#==) (k a) (k b)
fromCmpB (a :#!= b) k = liftA2 (#!=) (k a) (k b)
fromCmpB (a :#>  b) k = liftA2 (#>)  (k a) (k b)
fromCmpB (a :#>= b) k = liftA2 (#>=) (k a) (k b)
fromCmpB (a :#<  b) k = liftA2 (#<)  (k a) (k b)
fromCmpB (a :#<= b) k = liftA2 (#<=) (k a) (k b)

instance Member CmpB CmpB where uprism = id

instance Member CmpB r => CmpB_ (Comp r a) where
  a #== b = join (send (a :#== b))
  a #!= b = join (send (a :#!= b))
  a #>  b = join (send (a :#>  b))
  a #>= b = join (send (a :#>= b))
  a #<  b = join (send (a :#<  b))
  a #<= b = join (send (a :#<= b))
