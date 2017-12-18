{-# LANGUAGE FlexibleContexts #-}
module Types.Error
  ( DefnError(..)
  , PathError(..)
  , EvalError(..)
  )
where
  
import Types.Parser( Tag, Vis )
import qualified Text.Parsec as P( ParseError )

-- Expr error
data EvalError a b =
    UnboundVar b
  | NoField (Tag a)
  | DuplicateField (Tag a)
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
  

