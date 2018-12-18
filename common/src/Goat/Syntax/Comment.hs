{-# LANGUAGE TypeFamilies #-}
module Goat.Syntax.Comment
  where
  
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<|>))
  
infixr 0 #//, :#//
  
-- | Goat comments
class Comment_ r where
  type Ref r
  (#//) :: Ref r -> String -> r
  
data Comment r = r :#// String
  deriving (Eq, Show)
  
instance Comment_ (Comment r) where
  type Ref (Comment r) = r
  (#//) = (:#//)
  

-- | Parse a comment
comment :: Comment_ r => Parser (Ref r -> r)
comment = do
  Parsec.try (Parsec.string "//")
  s <- Parsec.manyTill Parsec.anyChar end
  return (#// s)
  where
    end = (Parsec.endOfLine *> return ()) <|> Parsec.eof

    
-- | Parse whitespace and comments
spaces :: Parser ()
spaces = do
  Parsec.spaces
  Parsec.optional (specialisedComment *> spaces)
  --Parsec.option (#// "") (comment *> spaces) 
  where
    specialisedComment :: Parser (r -> Comment r)
    specialisedComment = comment