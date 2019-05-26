module Goat.Interpreter.Browse where

import Goat.Lang.Parser (definition)


-- | Enter read-eval-print loop
browse
  :: IO ()
browse = first where
  first = getPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s =
    putStrLn (either
      (displayErrorList displayStaticError)
      (displayValue displayDyn')
      (readExpr s))
    >> first
   

-- | Parse and check expression

readExpr
  :: Text
  -> Either [ImportError] (Repr (Dyn DynError) Void)
readExpr t =
  case parse tokens "myi" t >>=
        parse (definition <* Text.Parsec.eof) "myi" of
    Left e -> Left (ParseError e)
    Right v -> 
  

-- Console / Import --
flushStr :: Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
getPrompt :: Text -> IO Text
getPrompt prompt =
  flushStr prompt >> T.getLine
  
  
  
