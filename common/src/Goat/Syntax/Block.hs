{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Syntax.Block
  where

import Goat.Co
import Goat.Syntax.Comment (spaces)
import Goat.Syntax.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<?>))

-- | Construct a block
class Block_ r where
  type Stmt r
  block_ :: [Stmt r] -> r

parseBlock :: Block_ r => Parser (Stmt r) -> Parser r
parseBlock s = block_ <$> braces (parseBody s)
  where
    braces = Parsec.between
      (Parsec.char '{' >> spaces)
      (Parsec.char '}' >> spaces)

data Block stmt a = Block [stmt] deriving (Eq, Show)

instance MemberU Block r => Block_ (Comp r a) where
  type Stmt (Comp r a) = Dep Block r
  block_ bdy = send (Block bdy)
    
showBlock
 :: (stmt -> ShowS)
 -> Comp (Block stmt <: t) ShowS -> Comp t ShowS
showBlock ss = handle (\ (Block bdy) _ ->
  return (showBlock' ss (Block bdy)))

showBlock' :: (stmt -> ShowS) -> Block stmt a -> ShowS
showBlock' ss (Block []) = showString "{}"
showBlock' ss (Block [s]) =
  showString "{ " . ss s . showString " }"
showBlock' ss (Block bdy) =
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
  handle (\ (Block bdy) _ ->
    return (block_ (fmap ks bdy)))

newtype SomeBlock stmt =
  SomeBlock {
    getBlock :: forall t a . Comp (Block stmt <: t) a
    }

instance Block_ (SomeBlock stmt) where
  type Stmt (SomeBlock stmt) = stmt
  block_ bdy = SomeBlock (block_ bdy)

runBlock :: Block_ s => (stmt -> Stmt s) -> SomeBlock stmt -> s
runBlock ks = run . fromBlock ks . getBlock

blockProof
 :: SomeBlock s -> SomeBlock s
blockProof = runBlock id

-- | A block body is a sequence of statements separated by ';'.
type Body s = [s]

parseBody :: Parser s -> Parser (Body s)
parseBody p = Parsec.sepEndBy p (Parsec.string ";" >> spaces)

showBody :: ShowS -> (s -> ShowS) -> Body s -> ShowS
showBody wsep sx [] = id
showBody wsep sx (x:xs) =
  sx x
    . foldr (\ x s -> showString ";" . wsep . sx x . s) id xs
