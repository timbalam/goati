{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Types.Error
  ( ScopeError(..)
  , ParseError(..)
  , ImportError(..)
  )
where

import qualified Text.Parsec as P( ParseError )

  
-- | Free parameter
newtype ScopeError a = ParamFree a
  deriving (Eq, Show)


-- Parser exception
data ParseError = ParseError P.ParseError
  deriving (Eq, Show)


-- ImportError exception
data ImportError = ImportError IOError
  deriving (Eq, Show)
  

