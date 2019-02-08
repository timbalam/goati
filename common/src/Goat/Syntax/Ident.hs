{-# LANGUAGE TypeOperators, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
module Goat.Syntax.Ident
  ( module Goat.Syntax.Ident
  , IsString(..)
  )
  where

import Goat.Co
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<?>), (<|>))
import Control.Applicative (liftA2)
import Data.String (IsString(..))
import qualified Data.Text as Text


-- | Represents a valid Goat identifier
parseIdent :: IsString r => Parser r
parseIdent =
  (do
    x <- Parsec.letter
    xs <- Parsec.many Parsec.alphaNum
    return (fromString (x:xs)))
      <?> "identifier"


newtype Ident a = Ident String deriving (Eq, Ord, Show)
  
instance DSend m => IsString ((m <<: Ident) t) where
  fromString s = case result of
    Left err -> error (show err)
    Right s  -> dsend (Ident s)
    where
      result = Parsec.parse
        (parseIdent <* Parsec.eof)
        ""
        (Text.pack s)

showIdent
 :: (DIter m, DView m, DVal m ~ ShowS) => (m <<: Ident) t -> m t
showIdent = dhandle (\ (Ident s) _ -> dpure (++ s))

fromIdent
 :: (DIter m, DView m, IsString (DVal m))
 => (m <<: Ident) t -> m t
fromIdent =
  dhandle (\ (Ident s) _ -> dpure (fromString s))


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