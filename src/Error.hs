module Error
  ( Error
  )
where
import Text.Parsec
 ( ParseError
 )

data Error = Parser ParseError | UnboundVar String | Default String

instance Show Error where
  show (Parser e) = "Parser error at " ++ show e
  show (UnboundVar v) = "Unbound variable: " ++ show v
  show (Default s) = show s