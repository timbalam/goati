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

readMy :: Parser a -> String -> Either String a
readMy parser input =
  case
    P.parse parser "myc" input
  of
  { Left err -> Left $ show err
  ; Right xs -> Right xs
  }

readProgram :: String -> String
readProgram s =
  case
    readMy program s
  of
  { Left msg -> msg
  ; Right xs -> foldr (\a b -> show a ++ "\n" ++ b) "" xs
  }
