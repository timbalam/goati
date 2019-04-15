{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Goat.Lang.Ident
  ( module Goat.Lang.Ident
  , IsString(..)
  )
  where

import Goat.Comp
import qualified Text.Parsec as Parsec
import Text.Parsec.Text (Parser)
import Text.Parsec ((<?>), (<|>))
import Control.Applicative (liftA2)
import Data.String (IsString(..))
import qualified Data.Text as Text
--import Data.Void (Void, absurd)


-- | Represents a valid Goat identifier
parseIdent :: IsString r => Parser r
parseIdent =
  (do
    x <- Parsec.letter
    xs <- Parsec.many Parsec.alphaNum
    return (fromString (x:xs)))
      <?> "identifier"

parseIdentEnd :: Parser ()
parseIdentEnd = Parsec.notFollowedBy Parsec.alphaNum

newtype Ident = Ident String deriving (Eq, Ord, Show)

ident :: (String -> r) -> Ident -> r
ident ki (Ident i) = ki i

instance IsString Ident where
  fromString s = case result of
    Left err -> error ("IsString Ident: " ++ show s)
    Right s  -> Ident s
    where
      result = Parsec.parse
        (parseIdent <* Parsec.eof)
        ""
        (Text.pack s)


newtype Var a = Var String deriving (Eq, Ord, Show)

instance IsString (Var a) where fromString s = Var s
  
showVar :: Var a -> ShowS
showVar (Var s) = showString s

fromVar :: IsString r => Var a -> r
fromVar (Var s) = fromString s

instance Member Var Var where uprism = id

instance Member Var r => IsString (Comp r a) where
  fromString s = send (Var s)


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