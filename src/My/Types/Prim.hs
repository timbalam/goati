module My.Types.IOPrim
  ( IOPrim(..), IOExpr, IOPrimTag(..)
  )
  where

import Data.IORef (IORef)
import System.IO (Handle, IOMode)


-- | An IO primitive for embedding in a my-language expression
data IOPrim k = IOPrim (IOPrimTag (IOExpr k)) (IOExpr k)


type IOExpr k = Expr k (IOPrim k)


-- | Primitive my language field tags
data IOPrimTag a =
    OpenFile IOMode
  | HGetLine Handle
  | HGetContents Handle
  | HPutStr Handle
  | NewMut
  | GetMut (IORef a)
  | SetMut (IORef a)
  deriving Eq
  
