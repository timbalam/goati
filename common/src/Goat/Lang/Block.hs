{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts, RankNTypes, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
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
  deriving (Eq, Show)

showBlock
 :: Applicative m => Block stmt a -> (stmt a -> m ShowS) -> m ShowS
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
 => Block stmt a -> (stmt a -> m (Stmt r)) -> m r
fromBlock (Block bdy) ks = block_ <$> traverse ks bdy

instance Member (Block stmt) (Block stmt) where uprism = id
instance MemberU Block (Block stmt) where
  type UIndex Block (Block stmt) = stmt

instance MemberU Block r => Block_ (Comp r a) where
  type Stmt (Comp r a) = UIndex Block r (Comp r a)
  block_ bdy = join (send (Block bdy))

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
