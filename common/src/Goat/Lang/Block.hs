{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts, RankNTypes, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.Block
  where

import Goat.Comp
import Goat.Lang.Comment (spaces)
import Goat.Lang.Symbol
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<?>))
import Control.Monad (join)
import Data.Void (Void)

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

data Block stmt a = Block [stmt a]
  deriving (Eq, Show, Functor, Foldable, Traversable)

showBlock
 :: (stmt a -> ShowS) -> Block stmt a -> ShowS
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
 :: Block_ r => (stmt a -> Stmt r) -> Block stmt a -> r
fromBlock ks (Block bdy) = block_ (ks <$> bdy)

instance Member (Block stmt) (Block stmt) where
  uprism = id
instance MemberU Block r => Block_ (Comp r a) where
  type Stmt (Comp r a) = UIndex Block r (Comp r a)
  block_ bdy = join (send (Block bdy))
    
showBlockC
 :: Traversable stmt
 => (stmt ShowS -> ShowS)
 -> Comp (Block stmt <: t) ShowS -> Comp t ShowS
showBlockC ss =
  handle (\ a k -> showBlock ss <$> traverse k a)

fromBlockC
 :: (Traversable stmt, Block_ r)
 => (stmt r -> Stmt r)
 -> Comp (Block stmt <: t) r -> Comp t r
fromBlockC ks =
  handle (\ a k -> fromBlock ks <$> traverse k a)

type SomeBlock stmt = Comp (Block stmt <: Null) Void

blockCProof
 :: Traversable s => SomeBlock s -> Comp (Block s <: t) a
blockCProof = handleAll (fromBlockC id)


-- | A block body is a sequence of statements separated by ';'.
type Body s = [s]

parseBody :: Parser s -> Parser (Body s)
parseBody p = Parsec.sepEndBy p (Parsec.string ";" >> spaces)

showBody :: ShowS -> (s -> ShowS) -> Body s -> ShowS
showBody wsep sx [] = id
showBody wsep sx (x:xs) =
  sx x
    . foldr (\ x s -> showString ";" . wsep . sx x . s) id xs
