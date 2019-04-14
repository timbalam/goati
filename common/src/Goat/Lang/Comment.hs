{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, DeriveFunctor, DeriveFoldable, DeriveTraversable, MultiParamTypeClasses #-}
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
  (#//) :: r -> String -> r

parseComment :: Comment_ r => Parser (r -> r)
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
    parseComment' :: Parser (Comp Comment r -> Comp Comment r)
    parseComment' = parseComment


data Comment a = a :#// String
  deriving (Eq, Show, Functor, Foldable, Traversable)

showComment :: (a -> ShowS) -> Comment a -> ShowS
showComment sa (a :#// s) =
  sa a .
    showString "//" .
    showString s .
    showChar '\n'

fromComment :: Comment_ r => (a -> r) -> Comment a -> r
fromComment ka (a :#// s) = ka a #// s

instance Member Comment Comment where uprism = id

instance Member Comment r => Comment_ (Comp r a) where
  r #// s = join (send (r :#// s))
