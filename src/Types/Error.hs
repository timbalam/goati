{-# LANGUAGE FlexibleContexts #-}
module Types.Error
  ( Field(..)
  , DefnOverlap(..)
  , Parse(..)
  )
where
  
import Types.Parser( Tag )
import Text.Parsec( ParseError )


-- Eval exception
data Eval a = 
    Unbound a
  | Undefined
  | Overlapping a
  deriving Show
  

-- Parser exception
data Parse = Parse ParseError
  deriving Show


-- ImportError exception
data Import = Import
  deriving Show

