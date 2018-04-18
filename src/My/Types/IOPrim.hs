module My.Types.IOPrim
  ( )
  where

import My.Types.Expr
import Data.IORef (IORef)
import System.IO (Handle, IOMode)


-- | An IO primitive for embedding in a my-language expression
data IOPrim a m b = IOPrim (IOPrimTag a)
  deriving (Functor, Foldable, Traversable)
  
  
instance MonadTrans (IOPrim a) where
  lift = IOPrim Pure
  
  
instance Bound (IOPrim a)



  
