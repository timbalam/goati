{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts #-}
module Goat.Syntax.Let
  where
  
import Goat.Syntax.Symbol
import Goat.Syntax.Field
  ( Field_(..), Field
  , Path_, Path, fromPath, showPath
  )
import Text.Parsec.Text (Parser)
import Data.String (IsString(..))
  
infix 1 #=, :#=

-- | Assignment
data Let lhs rhs a =
   NoLet a
 | lhs :#= rhs
 deriving (Eq, Show)

class Let_ s where
  type Lhs s
  type Rhs s
  (#=) :: Lhs s -> Rhs s -> s
  
instance Let_ (Let lhs rhs a) where
  type Lhs (Let lhs rhs a) = lhs
  type Rhs (Let lhs rhs a) = rhs
  
  (#=) = (:#=)
  
instance Field_ a => Field_ (Let lhs rhs a) where
  type Compound (Let lhs rhs a) = Compound a
  a #. i = NoLet (a #. i)
  
instance IsString a => IsString (Let lhs rhs a) where
  fromString s = NoLet (fromString s)

parseLet :: Let_ s => Parser (Lhs s -> Rhs s -> s)
parseLet = parseSymbol "=" >> return (#=)

showLet
 :: (lhs -> ShowS) -> (rhs -> ShowS) -> (a -> ShowS)
 -> Let lhs rhs a -> ShowS
showLet sl sr sa (NoLet a) = sa a
showLet sl sr sa (l :#= r) =
  sl l . showChar ' ' . showSymbol "=" . showChar ' ' . sr r

fromLet
 :: Let_ s
 => (lhs -> Lhs s) -> (rhs -> Rhs s) -> (a -> s)
 -> Let lhs rhs a -> s
fromLet kl kr ka (NoLet a) = ka a
fromLet kl kr ka (l :#= r) = kl l #= kr r

-- | Pun statement (define a path to equal the equivalent path in scope/ match
-- a path to an equivalent leaf pattern)
type Pun lcmp lhs rhs cmp a =
  Let (Path lcmp  lhs) rhs (Path cmp a)
type Pun_ s = (Let_ s, Path_ (Lhs s), Path_ s)
  -- s, Lhs s, Rhs s, Compound s, Compound (Lhs s)

showPun
 :: (lcmp -> ShowS)
 -> (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> (cmp -> ShowS)
 -> (a -> ShowS)
 -> Pun lcmp lhs rhs cmp a -> ShowS
showPun slc sl sr sc sa =
  showLet (showPath slc sl) sr (showPath sc sa)
  
-- | Parse a statement of a pattern block
parsePun
  :: Pun_ s
  => Parser (Compound (Lhs s))
  -> Parser (Lhs s)
  -> Parser (Rhs s)
  -> Parser (Compound s)
  -> Parser s
parsePun plc pl pr pc =
  do 
    l <- parsePath 
    -- alpha ...
    -- '.' alpha ...
    (do
      eq <- parseLet
      r <- pr
      return (fromPath absurd absurd l `eq` r))
      <|> return (fromPath absurd absurd l)

fromPun
 :: Pun_ r
 => (lcmp -> Compound (Lhs r))
 -> (lhs -> Lhs r)
 -> (rhs -> Rhs r)
 -> (cmp -> Compound r)
 -> (a -> r)
 -> Pun lcmp lhs rhs cmp a -> r
fromPun klc kl kr kc ka =
  fromLet (fromPath klc kl) kr (fromPath kc ka)

