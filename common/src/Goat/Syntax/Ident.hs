module Goat.Syntax.Ident
  where
  
import Goat.Syntax.Comment (spaces)
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<?>), (<|>))
import Control.Applicative (liftA2)
import Data.String (IsString(..))
import qualified Data.Text as Text
  

-- | Represents a valid Goat identifier
newtype Ident = Ident String deriving (Eq, Ord, Show)
  
instance IsString Ident where
  fromString s = case result of
      Left err -> error (show err)
      Right i  -> i
    where
      result = Parsec.parse
        (parseIdent <* Parsec.eof)
        ""
        (Text.pack s)

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