module Error
  ( Error(Parser, UnboundVar, PrimitiveOperation, Default)
  )
where
import Text.Parsec
 ( ParseError
 )

data Error = Parser String ParseError | UnboundVar String String | PrimitiveOperation String String | Default String

instance Show Error where
  show (Parser msg e) = msg ++ ": " ++ show e
  show (UnboundVar msg v) = show msg ++ ": " ++ show v
  show (PrimitiveOperation msg s) = show msg ++ ": " ++ show s
  show (Default msg) = show msg