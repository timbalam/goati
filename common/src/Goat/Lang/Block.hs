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
 :: Applicative m
 => (s -> m ShowS) ->  Block s a -> m ShowS
showBlock ss (Block []) = pure (showString "{}")
showBlock ss (Block [s]) =
  ss s <&> \ a -> showString "{ " . a . showString " }"
showBlock ss (Block bdy) =
  showBody wsep ss bdy <&> \ a ->
    showString "{\n    " . a . showString "\n}"
  where
    wsep = showString "\n    "

fromBlock
 :: (Applicative m, Block_ r)
 => (stmt -> m (Stmt r)) -> Block stmt a -> m r
fromBlock ks (Block bdy) = block_ <$> traverse ks bdy

instance Block_ (Block stmt a) where
  type Stmt (Block stmt a) = stmt
  block_ = Block

instance MemberU Block r => Block_ (Comp r a) where
  type Stmt (Comp r a) = UIndex Block r
  block_ bdy = send (Block bdy)

-- | A block body is a sequence of statements separated by ';'.
type Body s = [s]

parseBody :: Parser s -> Parser (Body s)
parseBody p = Parsec.sepEndBy p (Parsec.string ";" >> spaces)

showBody
 :: Applicative m => ShowS -> (s -> m ShowS) -> Body s -> m ShowS
showBody wsep sx [] = pure id
showBody wsep sx (x:xs) =
  liftA2
    (.)
    (sx x)
    (foldr (liftA2 showStmt . sx) (pure id) xs)
  where
    showStmt a s = showString ";" . wsep . a . s
