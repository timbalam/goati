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

data DefnError a b =
    OlappedMatch (PathError a (Tag a))
  | OlappedSet (PathError a b)
  deriving Show

  
data PathError a b =
    ErrorRoot
  | b `HasError` PathError a (Tag a)
  deriving Show


-- Parser exception
data ParseError = ParseError P.ParseError
  deriving Show


-- ImportError exception
data ImportError = ImportError
  deriving Show
  

