module Error
  ( Error(..)
  )
where
import Text.Parsec ( ParseError )

data Error = Parser String ParseError | UnboundVar String String | OverlappingDefinitions String String | PrimitiveOperation String String | ImportError String String | Default String

strMsg :: Error -> String
strMsg (Parser msg e) = msg ++ ": " ++ show e
strMsg (UnboundVar msg v) = msg ++ ": " ++ show v
strMsg (OverlappingDefinitions msg v) = msg ++ ": " ++ show v
strMsg (PrimitiveOperation msg s) = msg ++ ": " ++ show s
strMsg (ImportError msg v) = msg ++ ": " ++ v
strMsg (Default msg) = msg

instance Show Error where show = strMsg