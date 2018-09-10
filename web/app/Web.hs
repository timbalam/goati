module Main where

import My.Version (myiWebVersion)
import My.Syntax.Interpreter (parseDefns, parseExpr, evalAndShow, Browse(..))
import GHCJS.Foreign.Callback
import GHCJS.Types (JSVal)
import Data.JSString (JSString, pack)
import Data.JSString.Text (textFromJSVal)
import Data.Maybe (fromMaybe)

foreign import javascript unsafe
  "setup($1)"
  js_setup :: Callback (JSVal -> JSVal -> IO()) -> IO ()
  
foreign import javascript unsafe
  "appendResult($1, $2)"
  js_appendResult :: JSString -> JSString -> IO ()

  
main :: IO ()
main =
  do
    cb <- asyncCallback2 (\ code cmd ->
      evalDefns (textFromJSVal code) (textFromJSVal cmd) >>= js_appendResult cmd . pack)
    js_setup cb
    releaseCallback cb
  where
    evalDefns progt exprt = do
      Browse k _ <- parseDefns progt
      e <- parseExpr exprt
      return (evalAndShow (fromMaybe id k e))
      
