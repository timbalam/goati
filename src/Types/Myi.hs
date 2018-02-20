module Types.Myi( KeySource(..), K )
where
import Types.Expr( Tag )


data KeySource =
    File FilePath
  | User
  | Interpreter
  deriving (Eq, Ord, Show)

  
type K = Tag (KeySource, Int)
