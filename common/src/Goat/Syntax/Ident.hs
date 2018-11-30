{-# LANGUAGE OverloadedStrings #-}
module Goat.Syntax.Ident
  where
  
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<?>), (<|>))
import Control.Applicative (liftA2)
import Data.String (IsString(..))
import qualified Data.Text as Text
  

-- | Represents a valid Goat identifier
newtype Ident = Ident String deriving (Eq, Ord, Show)
  
instance IsString Ident where
  fromString s =
    case Parsec.parse (parseIdent <* Parsec.eof) "" (Text.pack s) of
      Left err -> error (show err)
      Right i  -> i

parseIdent :: Parser Ident
parseIdent =
  (do
    x <- Parsec.letter
    xs <- Parsec.many Parsec.alphaNum
    spaces
    return (Ident (x:xs)))
      <?> "identifier"

showIdent :: Ident -> ShowS
showIdent (Ident s) = (++ s)


-- | Parse a comment
comment :: Parser String
comment = do
  Parsec.try (Parsec.string "//")
  s <- Parsec.manyTill Parsec.anyChar end
  return s
  where
    end = (Parsec.endOfLine *> return ()) <|> Parsec.eof

    
-- | Parse whitespace and comments
spaces :: Parser ()
spaces = do
  Parsec.spaces
  Parsec.optional (comment *> spaces) 



-- | Alternative filepath style of ident with slashs to represent import paths
-- (deprecated)
parseIdentpath :: Parser Ident
parseIdentpath = (do
    x <- Parsec.letter
    xs <- rest
    spaces
    return (Ident (x:xs)))
    <?> "identifier"
  where
    rest = 
      alphanumnext <|> slashnext <|> return []
        
    alphanumnext = liftA2 (:) Parsec.alphaNum rest
      
    slashnext = do
      (c,x) <- Parsec.try
        (liftA2 (,) (Parsec.char '/') Parsec.letter)
      xs <- rest
      return (c:x:xs)