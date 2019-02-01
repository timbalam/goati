{-# LANGUAGE TypeFamilies, ConstraintKinds, FlexibleContexts #-}
module Goat.Syntax.Let
  where
  
import Goat.Syntax.Symbol
import Goat.Syntax.Field (Field_(..), Field, Path_, Path)
import Text.Parsec.Text (Parser)
import Data.String (IsString(..))
  
infix 1 #=, :#=

-- | Assignment
data Let lhs rhs a =
   Pun a
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
  a #. i = Pun (a #. i)
  
instance IsString a => IsString (Let lhs rhs a) where
  fromString s = Pun (fromString s)

parseLet :: Let_ s => Parser (Lhs s -> Rhs s -> s)
parseLet = parseSymbol "=" >> return (#=)

showLet
 :: (lhs -> ShowS) -> (rhs -> ShowS) -> (a -> ShowS)
 -> Let lhs rhs a -> ShowS
showLet sl sr sa (Pun a) = sa a
showLet sl sr sa (l :#= r) =
  sl l . showChar ' ' . showSymbol "=" . showChar ' ' . sr r

fromLet
 :: Let_ s
 => (lhs -> Lhs s) -> (rhs -> Rhs s) -> (a -> s)
 -> Let lhs rhs a -> s
fromLet kl kr ka (Pun a) = ka a
fromLet kl kr ka (l :#= r) = kl l #= kr r


-- | Pun statement (define a path to equal the equivalent path in scope/ match
-- a path to an equivalent leaf pattern)
type Pun lcmp lhs rhs cmp a = Let (Path lcmp lhs) rhs (Path cmp a)
type Pun_ s =
  (Let s, IsString s, Path_ s, IsString (Lhs s), Path_ (Lhs s))
  -- s, Lhs s, Rhs s, Compound s, Compound (Lhs s)

  
-- | Parse a statement of a block expression
pun
 :: ( Let s
    , IsString_ (Lhs s), Path_ (Lhs s)
    , IsString s, Path_ s
    ) => Parser (Rhs s) -> Parser s
pun p =
  do
    p <- localpath <|> relpath
    (do
      eq <- parseLet
      rhs <- p
      return (fromPath id id p `eq` rhs))
      <|> 
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