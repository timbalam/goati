{-# LANGUAGE TypeFamilies, DeriveFunctor #-}
module Goat.Syntax.Block
  where

import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Symbol (parseSymbol, showSymbol)
import Goat.Syntax.Field (Field_(..))
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<?>))

-- | Construct a block
data Block s a =
    NoBlock a
  | Block [s] deriving (Eq, Show, Functor)

class Block_ r where
  type Stmt r
  block_ :: [Stmt r] -> r
  
instance Block_ (Block s a) where
  type Stmt (Block s a) = s
  block_ = Block
  
instance Field_ a => Field_ (Block s a) where
  type Compound (Block s a) = Compound a
  c #. i = NoBlock (c #. i)

-- | Parse a block construction
parseBlock :: Block_ r => Parser (Stmt r) -> Parser r
parseBlock s = block_ <$> braces (parseBody s) <?> "block"
  where
    braces = Parsec.between
      (Parsec.char '{' >> spaces)
      (Parsec.char '}' >> spaces)


showBlock :: (s -> ShowS) -> (a -> ShowS) -> Block s a -> ShowS
showBlock sx sa (NoBlock a) = sa a
showBlock sx sa (Block []) = showString "{}"
showBlock sx sa (Block [x]) = showString "{ " . sx x . showString " }"
showBlock sx sa (Block (x:xs)) =
  showString "{\n    "
    . showBody wsep sx xs
    . showString "\n}"
  where
    wsep = showString "\n    "

fromBlock :: Block_ r => (s -> Stmt r) -> (a -> r) -> Block s a -> r
fromBlock kx ka (NoBlock a) = ka a
fromBlock kx ka (Block xs) = block_ (map kx xs)


-- | A block body is a sequence of statements separated by ';'.
parseBody :: Parser s -> Parser [s]
parseBody p = Parsec.sepEndBy p (Parsec.string ";" >> spaces)

showBody :: ShowS -> (s -> ShowS) -> [s] -> ShowS
showBody wsep sx [] = id
showBody wsep sx (x:xs) =
  sx x
    . foldr (\ x s -> showString ";" . wsep . sx x . s) id xs
