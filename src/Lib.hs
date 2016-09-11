module Lib
  ( readProgram
  ) where
import Parser
  ( program
  )
import Text.Parsec.String
  ( Parser
  )
import qualified Text.Parsec as P

readMy :: Parser a -> String -> String
readMy parser input =
  case
    P.parse parser "my" input
  of
  { Left err -> show err
  ; Right xs -> "ok"
  }

readProgram :: String -> String
readProgram = readMy program
