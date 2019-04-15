{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, MultiParamTypeClasses #-}
module Goat.Lang.Comment
  where

import Goat.Comp
import Goat.Util ((<&>))
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


data Comment a = a :#// String deriving (Eq, Show)

showComment :: Functor m => Comment a -> (a -> m ShowS) -> m ShowS
showComment (a :#// s) sa =
  sa a <&> \ s' -> 
    s' .
      showString "//" .
      showString s .
      showChar '\n'

fromComment
 :: (Functor m, Comment_ r) => Comment a -> (a -> m r) -> m r
fromComment (a :#// s) ka = ka a <&> (#// s)

instance Member Comment Comment where uprism = id

instance Member Comment r => Comment_ (Comp r a) where
  r #// s = join (send (r :#// s))
