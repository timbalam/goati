module Goat.Syntax.Ident
  ( module Goat.Syntax.Ident
  , IsString(..)
  )
  where

import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<?>), (<|>))
import Control.Applicative (liftA2)
import Data.String (IsString(..))
import qualified Data.Text as Text
  

-- | Represents a valid Goat identifier
data Ident a =
    NoIdent a
  | Ident String deriving (Eq, Ord, Show)
  
instance IsString (Ident a) where
  fromString s = case result of
    Left err -> error (show err)
    Right s  -> Ident s
    where
      result = Parsec.parse
        (parseIdent <* Parsec.eof)
        ""
        (Text.pack s)

showIdent :: (a -> ShowS) -> Ident a -> ShowS
showIdent sa (NoIdent a) = sa a
showIdent sa (Ident s) = (++ s)

fromIdent
  :: IsString r => (a -> r) -> Ident a -> r
fromIdent ka (NoIdent a) = ka a
fromIdent ka (Ident s) = fromString s

parseIdent :: IsString r => Parser r
parseIdent =
  (do
    x <- Parsec.letter
    xs <- Parsec.many Parsec.alphaNum
    return (fromString (x:xs)))
      <?> "identifier"


-- | Alternative filepath style of ident with slashs to represent import paths
-- (deprecated)
parseIdentpath :: IsString r => Parser r
parseIdentpath = (do
  x <- Parsec.letter
  xs <- rest
  return (fromString (x:xs)))
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