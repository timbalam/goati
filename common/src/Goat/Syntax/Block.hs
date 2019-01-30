{-# LANGUAGE TypeFamilies #-}
module Goat.Syntax.Block
  where

import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Symbol (parseSymbol, showSymbol)
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<?>))

-- | Construct a block
data Block s = Block [s] deriving (Eq, Show)

class Block_ r where
  type Stmt r
  block_ :: [Stmt r] -> r
  
instance Block_ (Block s) where
  type Stmt (Block s) = s
  block_ = Block

-- | Parse a block construction
parseBlock :: Block_ r => Parser (Stmt r) -> Parser r
parseBlock s = block_ <$> braces (parseBody s) <?> "block"
  where
    braces = Parsec.between
      (Parsec.char '{' >> spaces)
      (Parsec.char '}' >> spaces)


showBlock :: (s -> ShowS) -> Block s -> ShowS
showBlock sx (Block []) = showString "{}"
showBlock sx (Block [x]) = showString "{ " . sx x . showString " }"
showBlock sx (Block (x:xs)) =
  showString "{\n    "
    . showBody wsep sx xs
    . showString "\n}"
  where
    wsep = showString "\n    "

fromBlock :: Block_ r => (s -> Stmt r) -> Block s -> r
fromBlock kx (Block xs) = block_ (map kx xs)


-- | A block body is a sequence of statements separated by ';'.
parseBody :: Parser s -> Parser [s]
parseBody p = Parsec.sepEndBy p (Parsec.string ";" >> spaces)

showBody :: ShowS -> (s -> ShowS) -> [s] -> ShowS
showBody wsep sx [] = id
showBody wsep sx (x:xs) =
  sx x
    . foldr (\ x s -> showString ";" . wsep . sx x . s) id xs
