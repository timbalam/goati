{-# LANGUAGE FlexibleContexts #-}
module Types.Error
  ( 
  )
where
  
import Types.Parser( Tag )
import qualified Text.Parsec as P( ParseError )


-- Eval exception
data Eval a = 
    Unbound a
  | Undefined
  | Overlapping a
  deriving Show
  

-- Parser exception
data Parse = Parse P.ParseError
  deriving Show


-- ImportError exception
data Import = Import
  deriving Show

