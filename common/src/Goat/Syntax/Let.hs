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

instance Let_ (Comp (Let lhs rhs <: k) a) where
  type Lhs (Comp (Let lhs rhs <: k) a) = lhs
  type Rhs (Comp (Let lhs rhs <: k) a) = rhs
  
  l #= r = send (l :#= r)
  
instance Field_ (Comp k a)
 => Field_ (Comp (Let lhs rhs <: k) a) where
  type Compound (Comp (Let lhs rhs <: k) a) = Compound (Comp k a)
  a #. i = inj (a #. i)

instance IsString (Comp k a)
 => IsString (Comp (Let lhs rhs <: k) a) where
  fromString s = inj (fromString s)

showLet
 :: (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> Comp (Let lhs rhs <: k) ShowS -> Comp k ShowS
showLet sl sr = handle (\ a _ -> return (showLet' sl sr a))
 where
    showLet' sl sr (l :#= r) =
      sl l . showChar ' ' . showSymbol "=" . showChar ' ' . sr r

fromLet
 :: Let_ s
 => (lhs -> Lhs s)
 -> (rhs -> Rhs s)
 -> Comp (Let lhs rhs <: k) s -> Comp k s
fromLet kl kr = handle (\ (l :#= r) _ -> return (kl l #= kr r))


-- | Pun statement (define a path to equal the equivalent path in scope/ match
-- a path to an equivalent leaf pattern)
