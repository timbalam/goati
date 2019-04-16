{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts, RankNTypes, MultiParamTypeClasses #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Lang.Block
  where

import Goat.Comp
import Goat.Lang.Comment (spaces)
import Goat.Lang.Symbol
import Goat.Util ((<&>))
import Text.Parsec.Text (Parser)
import qualified Text.Parsec as Parsec
import Text.Parsec ((<?>))
import Control.Applicative (liftA2)
import Control.Monad (join)
import Data.Functor.Identity (Identity(..))
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

data Block stmt a = Block [stmt] deriving (Eq, Show)

showBlock
 :: Applicative m => Block s a -> (s -> m ShowS) -> m ShowS
showBlock (Block []) ss = pure (showString "{}")
showBlock (Block [s]) ss =
  ss s <&> \ a -> showString "{ " . a . showString " }"
showBlock (Block bdy) ss =
  showBody wsep bdy ss <&> \ a ->
    showString "{\n    " . a . showString "\n}"
  where
    wsep = showString "\n    "

fromBlock
 :: (Applicative m, Block_ r)
 => Block stmt a -> (stmt -> m (Stmt r)) -> m r
fromBlock (Block bdy) ks = block_ <$> traverse ks bdy

instance Block_ (Block s a) where
  type Stmt (Block s a) = s
  block_ = Block

cloneBlock :: Block_ r => Block (Stmt r) a -> r
cloneBlock b = runIdentity (fromBlock b pure)

-- | Trivial check for instance 'Block_ (Block s a)' with 'Stmt (Block s a) ~ s'
blockProof :: Block s a -> Block s b
blockProof = cloneBlock

instance Member (Block s) (Block s) where uprism = id
instance MemberU Block (Block s) where
  type UIndex Block (Block s) = s

instance MemberU Block r => Block_ (Comp r a) where
  type Stmt (Comp r a) = UIndex Block r
  block_ bdy = send (Block bdy)

-- | A block body is a sequence of statements separated by ';'.
type Body s = [s]

parseBody :: Parser s -> Parser (Body s)
parseBody p = Parsec.sepEndBy p (Parsec.string ";" >> spaces)

showBody
 :: Applicative m => ShowS -> Body s -> (s -> m ShowS) -> m ShowS
showBody wsep [] sx = pure id
showBody wsep (x:xs) sx =
  liftA2
    (.)
    (sx x)
    (foldr (liftA2 showStmt . sx) (pure id) xs)
  where
    showStmt a s = showString ";" . wsep . a . s
