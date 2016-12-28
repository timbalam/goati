module Error
  ( Error(..)
  )
where
import Text.Parsec
 ( ParseError
 )

data Error = Parser String ParseError | UnboundVar String String | PrimitiveOperation String String | Undef String | Default String

instance Show Error where
  show (Parser msg e) = msg ++ ": " ++ show e
  show (UnboundVar msg v) = show msg ++ ": " ++ show v
  show (PrimitiveOperation msg s) = show msg ++ ": " ++ show s
  show (Undef msg) = show msg
  show (Default msg) = show msg