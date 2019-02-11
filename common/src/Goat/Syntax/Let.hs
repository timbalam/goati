{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, FlexibleInstances #-}
module Goat.Syntax.Let
  where
  
import Goat.Syntax.Symbol
import Goat.Syntax.Field
  ( Field_(..), Field, fromField
  , Path_, Path, parsePath, fromPath, showPath, runPath
  , Chain_
  )
import Goat.Co
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
import Data.String (IsString(..))
import Data.Void (Void, absurd)
  
infix 1 #=, :#=

-- | Assignment
class Let_ s where
  type Lhs s
  type Rhs s
  (#=) :: Lhs s -> Rhs s -> s

parseLet :: Let_ s => Parser (Lhs s -> Rhs s -> s)
parseLet = parseSymbol "=" >> return (#=)

data Let lhs rhs a = lhs :#= rhs deriving (Eq, Show)

instance Let_ (Comp (Let lhs rhs <: t) a) where
  type Lhs (Comp (Let lhs rhs <: t) a) = lhs
  type Rhs (Comp (Let lhs rhs <: t) a) = rhs
  
  l #= r = send (l :#= r)
  
instance Field_ (Comp t a)
 => Field_ (Comp (Let lhs rhs <: t) a) where
  type Compound (Comp (Let lhs rhs <: t) a) =
    Compound (Comp t a)
  a #. i = inj (a #. i)

instance IsString (Comp t a)
 => IsString (Comp (Let lhs rhs <: t) a) where
  fromString s = inj (fromString s)

showLet
 :: (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> (Comp t ShowS -> ShowS)
 -> Comp (Let lhs rhs <: t) ShowS -> ShowS
showLet sl sr st =
  st 
  . handle (\ a _ -> return (showLet' sl sr a))

showLet'
 :: (lhs -> ShowS) -> (rhs -> ShowS) -> Let lhs rhs a -> ShowS
showLet' sl sr (l :#= r) =
  sl l . showChar ' ' . showSymbol "=" . showChar ' ' . sr r

fromLet
 :: Let_ s
 => (lhs -> Lhs s)
 -> (rhs -> Rhs s)
 -> (Comp t s -> s)
 -> Comp (Let lhs rhs <: t) s -> s
fromLet kl kr kt =
  kt
  . handle (\ (l :#= r) _ -> return (kl l #= kr r))
