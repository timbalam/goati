{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts, RankNTypes #-}
module Goat.Lang.Comment
  where

import Goat.Comp
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
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
    parseComment' :: Parser (r -> SomeComment r)
    parseComment' = parseComment


data Comment ref a = ref :#// String deriving (Eq, Show)
  
instance MemberU Comment r => Comment_ (Comp r a) where
  type Ref (Comp r a) = Dep Comment r
  r #// s = send (r :#// s)

showComment
 :: (ref -> ShowS) -> Comp (Comment ref <: t) ShowS -> Comp t ShowS
showComment sr = handle (\ (r :#// s) _ ->
  return
    (sr r 
      . showString "//"
      . showString s
      . showChar '\n'))

fromComment
 :: Comment_ r
 => (ref -> Ref r)
 -> Comp (Comment ref <: t) r -> Comp t r
fromComment kr = handle (\ (r :#// s) _ -> return (kr r #// s))

newtype SomeComment ref =
  SomeComment {
    getComment :: forall t a. Comp (Comment ref <: t) a
    }

instance Comment_ (SomeComment ref) where
  type Ref (SomeComment ref) = ref
  r #// s = SomeComment (r #// s)

commentProof :: SomeComment r -> SomeComment r
commentProof = run . fromComment id . getComment
