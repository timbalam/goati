module My.Types.Prim
  where

import System.IO (Handle)

-- | Primitive my language field tags
data PrimTag = 
    NAdd Double
  | NSub Double
  | NProd Double
  | NDiv Double
  | NPow Double
  | NEq Double
  | NNe Double
  | NLt Double
  | NGt Double
  | NLe Double
  | NGe Double
  | HGetLine Handle
  | HGetContents Handle
  | HPutStr Handle
  | HPutChar Handle
  deriving (Eq, Show)

      
