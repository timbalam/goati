{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Types.Error
  ( ExprError(..)
  , PathError(..), listPaths
  , EvalError(..)
  , ScopeError(..)
  , ParseError(..)
  , ImportError(..)
  , Collect(..)
  )
where
  
import Types.Parser( Tag, Path, Vis, Field(..) )

import qualified Text.Parsec as P( ParseError )
import Data.Bifunctor
import Data.Semigroup
import Data.List.NonEmpty( NonEmpty )
import qualified Data.Map as M
import Control.Monad.Free


-- Wrapper for Either with specialised Applicative instance and 
-- Monoid instances
newtype Collect a b = Collect { getCollect :: Either a b }
  deriving (Functor, Bifunctor)

instance Semigroup m => Applicative (Collect m) where
  pure = Collect . Right
  
  Collect (Left m1) <*> Collect (Left m2) = (Collect . Left) (m1 <> m2)
  Collect (Left m) <*> _                  = Collect (Left m)
  Collect _        <*> Collect (Left m)   = Collect (Left m)
  Collect (Right f) <*> Collect (Right a) = (Collect . Right) (f a)
  
  
-- Evaluation error
data EvalError a =
    LookupFailed (Tag a)
--  | ConcatFieldsConflict (NonEmpty (Tag a))
--  | UpdateFieldsMissing (NonEmpty (Tag a))
--  | ParamUndefined (Vis a)
  deriving (Eq, Show)
  
  
newtype ScopeError a = ParamFree a
  deriving (Eq, Show)
  

data ExprError a b =
    OlappedMatch (PathError a (Tag a))
  | OlappedSet (PathError a (Vis a))
  deriving (Eq, Show)

  
data PathError a b = PathError (M.Map b (PathError a (Tag a)))
  deriving (Eq, Show)
  
  
listPaths :: PathError a b -> [Path a b]
listPaths (PathError m) = M.foldMapWithKey (go . Pure) m where
  go :: Path a b -> PathError a (Tag a) -> [Path a b]
  go p (PathError m) = if M.null m then [p] else 
    M.foldMapWithKey (go . Free . At p) m
  
  
instance (Ord a, Ord b) => Semigroup (PathError a b) where
  PathError a <> PathError b =
    PathError (M.unionWith (<>) a b)


-- Parser exception
data ParseError = ParseError P.ParseError
  deriving (Eq, Show)


-- ImportError exception
data ImportError = ImportError IOError
  deriving (Eq, Show)
  

