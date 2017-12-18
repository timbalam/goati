{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Types.Error
  ( DefnError(..)
  , PathError(..)
  , EvalError(..)
  , Collect(..)
  )
where
  
import Types.Parser( Tag, Vis )
import qualified Text.Parsec as P( ParseError )

import Data.Bifunctor
import Data.Monoid( (<>) )


-- Wrapper for Either with specialised Applicative instance and 
-- Monoid instances
newtype Collect a b = Collect { getCollect :: Either a b }
  deriving (Functor, Bifunctor)

instance Monoid m => Applicative (Collect m) where
  pure = Collect . Right
  
  Collect (Left m1) <*> Collect (Left m2) = (Collect . Left) (m1 <> m2)
  Collect (Left m) <*> _                  = Collect (Left m)
  Collect _        <*> Collect (Left m)   = Collect (Left m)
  Collect (Right f) <*> Collect (Right a) = (Collect . Right) (f a)
  
  
-- Evaluation error
data EvalError a b =
    UnboundVar b
  | Missing (Tag a)
  | Overlapped (Tag a)
  deriving (Eq, Show)
  

data DefnError a b =
    OlappedMatch (PathError a (Tag a))
  | OlappedSet (PathError a b)
  deriving (Eq, Show)

  
data PathError a b =
    ErrorRoot
  | b `HasError` PathError a (Tag a)
  deriving (Eq, Show)


-- Parser exception
data ParseError = ParseError P.ParseError
  deriving (Eq, Show)


-- ImportError exception
data ImportError = ImportError
  deriving (Eq, Show)
  

