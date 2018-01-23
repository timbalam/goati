{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Types.Error
  ( ParseError(..)
  , ImportError(..)
  )
where

import qualified Text.Parsec


-- Parser exception
data ParseError = ParseError Text.Parsec.ParseError
  deriving (Eq, Show)


-- ImportError exception
data ImportError = ImportError IOError
  deriving (Eq, Show)
  

