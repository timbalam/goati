{-# LANGUAGE TypeFamilies #-}
module Goat.Syntax.Let
  where
  
import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
  
infixr 1 #=, :#=

-- | Assignment
data Let a b = a :#= b deriving (Eq, Show)

class Let_ s where
  type Lhs s
  type Rhs s
  (#=) :: Lhs s -> Rhs s -> s
  
instance Let_ (Let a b) where
  type Lhs (Let a b) = a
  type Rhs (Let a b) = b
  
  (#=) = (:#=)

parseLet :: Let_ s => Parser (Lhs s -> Rhs s -> s)
parseLet = parseSymbol "=" >> return (#=)

showLet :: (a -> ShowS) -> (b -> ShowS) -> Let a b -> ShowS
showLet sa sb (a :#= b) =
  sa a . showChar ' ' . showSymbol "=" . showChar ' ' . sb b

fromLet :: Let_ s => (a -> Lhs s) -> (b -> Rhs s) -> Let a b -> s
fromLet ka kb (a :#= b) = ka a #= kb b