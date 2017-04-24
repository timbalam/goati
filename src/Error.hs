module Error
  ( Error(..)
  )
where
import Text.Parsec
 ( ParseError
 )

data Error = Parser String ParseError | UnboundVar String String | MultipleDefinitions String String | PrimitiveOperation String String | ImportError String String | Default String

instance Show Error where
  show (Parser msg e) = msg ++ ": " ++ show e
  show (UnboundVar msg v) = show msg ++ ": " ++ show v
  show (MultipleDefinitions msg v) = show msg ++ ": " ++ show v
  show (PrimitiveOperation msg s) = show msg ++ ": " ++ show s
  show (ImportError msg v) = show msg ++ ": " ++ v
  show (Default msg) = show msg