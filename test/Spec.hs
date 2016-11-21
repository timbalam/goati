import qualified Test.Parser as P
import qualified Types.Parser as T

import Control.Monad
  ( sequence_
  )

main :: IO ()
main = 
  sequence_
    [ P.testParser "\"hi\"" $ T.Rnode [T.Eval (T.String "hi")]
    , P.testParser "\"one\" \"two\"" $ T.Rnode [T.Eval (T.String "onetwo")]
    , P.testParser "123" $ T.Rnode [T.Eval (T.Number 123)]
    , P.testParser "123." $ T.Rnode [T.Eval (T.Number 123)]
    , P.testParser "123.0" $ T.Rnode [T.Eval (T.Number 123)]
    , P.testParser "1_000.2_5" $ T.Rnode [T.Eval (T.Number 1000.25)]
    ]
