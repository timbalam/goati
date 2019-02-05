{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts, TypeOperators, FlexibleInstances #-}
module Goat.Syntax.Let
  where
  
import Goat.Syntax.Symbol
import Goat.Syntax.Field
  ( Field_(..), Field, fromField
  , Path_, Path, parsePath, fromPath, showPath
  , Chain_
  )
import Goat.Co
  ( Comp, runComp, (<:)(..), Null, handle, send, inj )
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
showLet sl sr = handle (\ a _ -> return (showLet' sl sr a)) where
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
--type RelPath_ s = (Path_ s, IsString (Compound s))
type Pun_ s = (Let_ s, Path_ (Lhs s), Path_ s)
  -- s, Lhs s, Rhs s, Compound s, Compound (Lhs s)
  
-- | Parse a statement of a pattern block
parsePun
  :: Pun_ s
  => Parser (Compound s -> Lhs s)
  -> Parser (Rhs s)
  -> Parser (Compound s -> s)
parsePun pkl pr =
  do 
    lf <- parsePath
    (do
      kl <- pkl
      eq <- parseLet
      r <- pr
      return (\ c -> kl (runPath (lf c)) `eq` r))
      <|> return (runPath . lf)
  where
    runPath
     :: Path_ s
     => Comp (Field (Compound s) <: Null) Void -> s
    runPath m = runComp (fromField id (fmap absurd m))

type Pun klcmp lcmp klhs lhs rhs kcmp cmp k =
  Let (Comp (Path klcmp lcmp <: klhs) lhs) rhs
    <: Path kcmp cmp <: k

showPun
  :: (Comp klcmp ShowS -> ShowS)
  -> (Comp klhs ShowS -> ShowS)
  -> (rhs -> ShowS)
  -> (Comp kcmp ShowS -> ShowS)
  -> Comp (Pun klcmp ShowS klhs ShowS rhs kcmp ShowS k) ShowS
  -> Comp k ShowS
showPun sklc skl sr skc =
  showPath skc . showLet (skl . showPath sklc) sr

fromPun
  :: Pun_ s
  => (Comp klcmp (Compound (Lhs s)) -> Compound (Lhs s))
  -> (Comp klhs (Lhs s) -> Lhs s)
  -> (rhs -> Rhs s)
  -> (Comp kcmp (Compound s) -> Compound s)
  -> Comp
      (Pun
        klcmp
        (Compound (Lhs s))
        klhs
        (Lhs s)
        rhs
        kcmp
        (Compound s)
        k)
      s
  -> Comp k s
fromPun kklc kkl kr kkc =
  fromPath kkc . fromLet (kkl . fromPath kklc) kr
