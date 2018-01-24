{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Types.Error
  ()
where


-- ImportError exception
data ImportError = ImportError IOError
  deriving (Eq, Show)
  

