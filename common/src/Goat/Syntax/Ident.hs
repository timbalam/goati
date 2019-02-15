{-# LANGUAGE TypeOperators, FlexibleInstances, FlexibleContexts, TypeFamilies, RankNTypes #-}
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
  
instance IsString (Comp (Ident <: t) a) where
  fromString s = case result of
    Left err -> fail (show err)
    Right s  -> send (Ident s)
    where
      result = Parsec.parse
        (parseIdent <* Parsec.eof)
        ""
        (Text.pack s)

showIdent
 :: Comp (Ident <: t) ShowS -> Comp t ShowS
showIdent = handle (\ (Ident s) _ -> return (showString s))

fromIdent
 :: IsString r
 => Comp (Ident <: t) r -> Comp t r
fromIdent = handle (\ (Ident s) _ -> return (fromString s))

newtype SomeIdent =
  SomeIdent { getIdent :: forall t a . Comp (Ident <: t) a }

instance IsString SomeIdent where
  fromString s = SomeIdent (fromString s)

identProof :: SomeIdent -> SomeIdent
identProof = run . fromIdent . getIdent


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