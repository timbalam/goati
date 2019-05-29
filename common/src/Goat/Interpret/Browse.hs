{-# LANGUAGE OverloadedStrings #-}
module Goat.Interpret.Browse where

import Goat.Lang.Parser (definition, tokens, eof, parse)
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval
  ( checkExpr, eval
  , Repr, Import(..), VarName
  , displayValue
  , Ident, Identity, Multi
  )
import Goat.Error (ImportError(..), displayImportError)
import Data.Bifunctor (bimap)
--import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Data.Text (Text)
import Data.Void (Void)
import System.IO (hFlush, stdout, FilePath)
-- import qualified Text.Parsec as Parsec


-- | Enter read-eval-print loop
browse
  :: String -> IO ()
browse src = first where
  first = getPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s =
    putStrLn
      (either
        displayImportError
        (displayValue . snd . checkExpr)
        (parseExpr src s))
    >> first
   

-- | Parse and check expression

parseExpr
  :: String
  -> Text
  -> Either ImportError
      (Repr (Multi Identity) (VarName Ident Ident (Import Ident)))
parseExpr src t =
  bimap
    ParseError
    getDefinition
    (parse tokens src t >>=
      parse (definition <* eof) src)
  

-- Console / Import --
flushStr :: Text -> IO ()
flushStr s =
  Text.putStr s >> hFlush stdout

getPrompt :: Text -> IO Text
getPrompt prompt =
  flushStr prompt >> Text.getLine
