module Error
  ( Error(..)
  )
where
import Text.Parsec
 ( ParseError
 )

data Error = Parser ParseError | UnboundVar String | PrimitiveOperation String | Default String

instance Show Error where
  show (Parser e) = "Parser error at " ++ show e
  show (UnboundVar v) = "Unbound variable: " ++ show v
  show (PrimitiveOperation s) = show s
  show (Default s) = show s