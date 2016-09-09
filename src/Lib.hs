module Lib
  ( read
  , readProgram
  ) where
import Myc.Parser
  ( program
  )
import Text.Parsec
  ( parser
  )

read :: Parser a -> String -> String
read parser input =
  case
    parse parser "my" input
  of
    Left err -> "error"
    Right xs -> "ok"

readProgram = read program
