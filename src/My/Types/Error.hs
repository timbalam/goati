{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}

module My.Types.Error
  ()
where


-- ImportError exception
data ImportError = ImportError IOError
  deriving (Eq, Show)
  

