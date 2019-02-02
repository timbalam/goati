{-# LANGUAGE TypeFamilies #-}
module Goat.Syntax.Comment
  where

import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
import Data.Void (Void)
  
infixr 0 #//, :#//
  
-- | Goat comments
data Comment ref a =
    NoComment a
  | ref :#// String
  deriving (Eq, Show)

class Comment_ r where
  type Ref r
  (#//) :: Ref r -> String -> r
  
instance Comment_ (Comment ref a) where
  type Ref (Comment ref a) = ref
  (#//) = (:#//)
  
showComment
 :: (ref -> ShowS) -> (a -> ShowS) -> Comment ref a -> ShowS
showComment sr sa (NoComment a) = sa a
showComment sr sa (r :#// s) = sr r 
  . showString "//"
  . showString s
  . showChar '\n'


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
  Parsec.optional (parseComment' *> spaces)
  --Parsec.option (#// "") (parseComment *> spaces) 
  where
    parseComment' :: Parser (r -> Comment r Void)
    parseComment' = parseComment