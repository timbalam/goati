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
class Block_ r where
  type Stmt r
  block_ :: [Stmt r] -> r

parseBlock :: Block_ r => Parser (Stmt r) -> Parser r
parseBlock s = block_ <$> braces (parseBody s) <?> "block"
  where
    braces = Parsec.between
      (Parsec.char '{' >> spaces)
      (Parsec.char '}' >> spaces)

data Block stmt a = Block [stmt] deriving (Eq, Show)

instance Block_ (Comp (Block stmt <: t) a) where
  type Stmt (Comp (Block stmt <: t) a) = stmt
  block_ bdy = send (Block bdy)
  
instance Field_ (Comp t a)
 => Field_ (Comp (Block s <: t) a) where
  type Compound (Comp (Block s <: t) a) = Compound (Comp t a)
  c #. i = inj (c #. i)


showBlock
 :: (stmt -> ShowS)
 -> Comp (Block stmt <: t) ShowS -> Comp t ShowS
showBlock ss = handle (\ b _ -> return (showBlock' ss b))

showBlock' :: (stmt -> ShowS) -> Block stmt a -> ShowS
showBlock ss (Block []) = showString "{}"
showBlock ss (Block [s]) =
  showString "{ " . ss s . showString " }"
showBlock ss (Block bdy) =
  showString "{\n    "
    . showBody wsep ss bdy
    . showString "\n}"
  where
    wsep = showString "\n    "

fromBlock
 :: Block_ r
 => (stmt -> Stmt r)
 -> Comp (Block stmt <: t) r -> Comp t r
fromBlock ks =
  handle (\ (Block bdy) _ -> return (block_ (map ks bdy)))


-- | A block body is a sequence of statements separated by ';'.
type Body s = [s]

parseBody :: Parser s -> Parser (Body s)
parseBody p = Parsec.sepEndBy p (Parsec.string ";" >> spaces)

showBody :: ShowS -> (s -> ShowS) -> Body s -> ShowS
showBody wsep sx [] = id
showBody wsep sx (x:xs) =
  sx x
    . foldr (\ x s -> showString ";" . wsep . sx x . s) id xs
