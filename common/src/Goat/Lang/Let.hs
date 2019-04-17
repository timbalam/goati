{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, FlexibleInstances, RankNTypes #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.Let
  where
  
import Goat.Comp
import Goat.Lang.Symbol
import Control.Applicative (liftA2)
import Text.Parsec.Text (Parser)
  
infix 1 #=, :#=

-- | Assignment
class Let_ s where
  type Lhs s
  type Rhs s
  (#=) :: Lhs s -> Rhs s -> s

parseLet :: Let_ s => Parser (Lhs s -> Rhs s -> s)
parseLet = parseSymbol "=" >> return (#=)

data Let lhs rhs a = lhs :#= rhs deriving (Eq, Show)

showLet
 :: Applicative m
 => (lhs -> m ShowS)
 -> (rhs -> m ShowS)
 -> Let lhs rhs a -> m ShowS
showLet sl sr (l :#= r) = 
  liftA2 showLet' (sl l) (sr r)
  where
    showLet' a b =
      a . showChar ' ' . showSymbol "=" . showChar ' ' . b

fromLet
 :: (Applicative m, Let_ s)
 => (lhs -> m (Lhs s))
 -> (rhs -> m (Rhs s))
 -> Let lhs rhs a -> m s
fromLet kl kr (l :#= r) = liftA2 (#=) (kl l) (kr r)

instance MemberU2 Let r => Let_ (Comp r a) where
  type Lhs (Comp r a) = U2Index Let r
  type Rhs (Comp r a) = U1Index Let r
  l #= r = send (l :#= r)
