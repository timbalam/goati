{-# LANGUAGE OverloadedStrings #-}
module Goat.Interpret.Browse where

import Goat.Lang.Parser
  ( definition, tokens, eof, parse )
import Goat.Repr.Lang (getDefinition)
import Goat.Repr.Eval
  ( checkExpr, displayExpr
  , Repr, AnnDefns, AnnCpts, Trail, View
  , VarName, Ident, Import(..)
  , MemoRepr, DynCpts, DynError, Void
  )
import Goat.Lang.Error
  ( ImportError(..), displayImportError )
import Data.Bifunctor (bimap)
import qualified Data.Text.IO as Text
import Data.Text (Text)
import System.IO (hFlush, stdout, FilePath)


-- | Enter read-eval-print loop
browse
  :: String -> IO ()
browse src = first
  where
  first = getPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s
    = putStrLn
        (either
          displayImportError
          (displayMemo . snd . checkExpr)
          (parseBrowse src s))
    >> first
  
  displayMemo
   :: MemoRepr Void -> String
  displayMemo = displayExpr
  
   

-- | Parse and check expression

parseBrowse
 :: String
 -> Text
 -> Either ImportError
      (Repr
        (AnnDefns
          [View (Trail Ident)]
          [Trail Ident]
          (AnnCpts [Ident])
          Ident)
        ()
        (VarName Ident Ident (Import Ident)))
parseBrowse src t
  = bimap
      ParseError
      getDefinition
      (parse tokens src t
       >>= parse (definition <* eof) src)
  

-- Console / Import --
flushStr :: Text -> IO ()
flushStr s
  = Text.putStr s >> hFlush stdout

getPrompt :: Text -> IO Text
getPrompt prompt
  = flushStr prompt >> Text.getLine
