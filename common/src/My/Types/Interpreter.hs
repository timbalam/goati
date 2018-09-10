-- | Interpreter implementation details

module My.Types.Interpreter (KeySource(..), K)
where
import My.Types.Repr (Tag)

-- | Unforgeable symbolic keys useable as fields for my language values
type K = Tag (KeySource, Int)

   
-- | Track the source for which a key is generated
--
--   Keys for each source can be generated independently allowing e.g. 
--   parallel processing of import files (not implemented)
data KeySource =
    File FilePath
  | User
  | Interpreter
  deriving (Eq, Ord, Show)

