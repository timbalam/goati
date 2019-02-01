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
  
-- | Let statement (define a path to be equal to a value / match a path to
-- a pattern)
type LetMatch lcmp lhs rhs a = Let (Path lcmp lhs) rhs a
type LetMatch_ s = (Let_ s, Path_ (Lhs s))

showLetMatch
 :: (lcmp -> ShowS)
 -> (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> (a -> ShowS)
 -> LetMatch lcmp lhs rhs a -> ShowS
showLetMatch slc sl sr sa =
  showLet (showPath slc sl) sr sa

fromLetMatch
 :: LetMatch_ s
 => (lcmp -> Compound (Lhs s))
 -> (lhs -> Lhs s)
 -> (rhs -> Rhs s)
 -> (a -> s)
 -> LetMatch lcmp lhs rhs a -> s
fromLetMatch klc kl kr ka =
  fromLet (fromPath klc kl) kr ka

-- | Let pattern statement (define a pattern to be equal to a value)
--type LetPatt s = (Let_ s, Patt_ (Lhs s))

-- | Pun statement (define a path to equal the equivalent path in scope/ match
-- a path to an equivalent leaf pattern)
type Pun lcmp lhs rhs cmp a = LetMatch lcmp lhs rhs (Path cmp a)
type Pun_ s =
  (LetMatch_ s, IsString s, Path_ s)
  -- s, Lhs s, Rhs s, Compound s, Compound (Lhs s)
  
showPun
 :: (lcmp -> ShowS)
 -> (lhs -> ShowS)
 -> (rhs -> ShowS)
 -> (cmp -> ShowS)
 -> (a -> ShowS)
 -> Pun lcmp lhs rhs cmp a -> ShowS
showPun slc sl sr sc sa =
  showLetMatch slc sl sr (showPath sc sa)
  
fromPun
 :: Pun_ r
 => (lcmp -> Compound (Lhs r))
 -> (lhs -> Lhs r)
 -> (rhs -> Rhs r)
 -> (cmp -> Compound r)
 -> (a -> r)
 -> Pun lcmp lhs rhs cmp a -> r
fromPun klc kl kr kc ka =
  fromLetMatch klc kl kr (fromPath kc ka)

{-
-- | Parse a statement of a block expression
parsePun
 :: ( Let s
    , IsString_ (Lhs s), Path_ (Lhs s)
    , IsString s, Path_ s
    ) => Parser (Path Void Void -> Rhs s) -> Parser s
parsePun p =
  do
    p <- localpath <|> relpath
    (do
      eq <- parseLet
      rhs <- p
      return (fromPath absurd absurd p `eq` rhs))
      <|> return (fromPath absurd absurd p)
  where
    identFirst :: forall x . (IsString_ x, Path_ x) => x
    identFirst = do
      Ident s <- parseIdent
      (do
        f <- parseChain1
        return (f (fromString s)))
        
      <|> return (fromString s)
        (do
          eq <- parseLet
          rhs <- p
          return (f (fromString s) `eq` rhs))
        <|> return (f (fromString s)))
        
    letNext
      :: Compound (Lhs r) -> (Compound (Lhs r) -> Lhs r) -> r
    letNext s f =
      (do
        
      
  f <- relpath <|> localpath
  pubfirst          -- '.' alpha ...
    <|> pattfirst   -- alpha ...
                    -- '(' ...
    <|> escfirst    -- '^' ...
    <?> "statement"
  where
    pubfirst = do
      ARelPath apath <- relpath
      ((`id` apath) <$> pattrest <**> assign <*> p  -- '{' ...
                                                    -- '=' ...
        <|> return apath)
      
    pattfirst =
      (localpath      -- alpha ...
        <|> pattblock)  -- '{' ...
        <**> pattrest <**> assign <*> p
      
    pattrest :: Patt p => Parser (p -> p)
    pattrest = iter (liftA2 flip extend pattblock)
          
    pattblock
      :: (Block p, Pun (Stmt p), LetMatch (Stmt p), Patt (Lower (Rhs (Stmt p))))
      => Parser p
    pattblock = block (match patt) 
    
    patt :: Patt p => Parser p 
    patt =
      (relpath          -- '.' alpha
        <|> localpath   -- alpha
        <|> pattblock)  -- '{'
        <**> pattrest
        <?> "pattern"
        
    escfirst = esc <*>
      (localpath         -- '.' alpha ..
        <|> relpath)     -- alpha ...
-}
