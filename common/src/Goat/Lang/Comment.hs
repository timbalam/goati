{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts, RankNTypes, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Goat.Lang.Comment
  where

import Goat.Comp
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
import Control.Monad (join)
import Data.Void (Void)
  
infixr 0 #//, :#//
  
-- | Goat comments
class Comment_ r where
  type Ref r
  (#//) :: Ref r -> String -> r

parseComment :: Comment_ r => Parser (Ref r -> r)
parseComment = do
  Parsec.try (Parsec.string "//")
  s <- Parsec.manyTill Parsec.anyChar end
  return (#// s)
  where
    end = (Parsec.endOfLine *> return ()) <|> Parsec.eof


-- | Parse whitespace and comments
spaces :: Parser ()
spaces = do
  Parsec.spaces
  Parsec.many (parseComment' *> Parsec.spaces)
  return ()
  --Parsec.option (#// "") (parseComment *> spaces) 
  where
    parseComment' :: Parser (r -> Comment r)
    parseComment' = parseComment


data Comment a = a :#// String
  deriving (Eq, Show, Functor, Foldable, Traversable)

showComment :: (a -> ShowS) -> Comment a -> ShowS
showComment sa (a :#// s) =
  sa a .
    showString "//" .
    showString s .
    showChar '\n'

fromComment :: Comment_ r => (a -> Ref r) -> Comment a -> r
fromComment ka (a :#// s) = ka a #// s

commentProof :: Comment a -> Comment a
commentProof = fromComment id

instance Comment_ (Comment a) where
  type Ref (Comment a) = a
  r #// s = r :#// s

instance Member Comment r => Comment_ (Union r a) where
  type Ref (Union r a) = a
  r #// s = injU (r :#// s)

instance Member Comment r => Comment_ (Comp r a) where
  type Ref (Comp r a) = Comp r a
  r #// s = join (send (r :#// s))

showCommentC
 :: Comp (Comment <: t) ShowS -> Comp t ShowS
showCommentC =
  handle (\ a k -> showComment id <$> traverse k a)

fromCommentC
 :: (Comment_ r, Ref r ~ r)
 => Comp (Comment <: t) r -> Comp t r
fromCommentC = handle (\ a k -> fromComment id <$> traverse k a)

commentCProof :: Comp (Comment <: Null) Void -> Comp (Comment <: t) a
commentCProof = handleAll (fromCommentC)
