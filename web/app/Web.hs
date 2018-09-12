module Main where

import My.Version (myiWebVersion)
import My.Util ( (<&>) )
import My.Syntax.Interpreter (runStmts, Repr(..), Prim(..))
import GHCJS.Foreign.Callback
import GHCJS.Types (JSVal)
import Data.JSString (JSString, pack)
import Data.JSString.Text (textFromJSVal, textToJSString)
import Data.Maybe (fromMaybe)
import Control.Exception.Base (catch, Exception(..), SomeException)

foreign import javascript unsafe
  "setup($1)"
  js_setup :: Callback (JSVal -> JSVal -> IO()) -> IO ()
  
foreign import javascript unsafe
  "$1.textContent = $2"
  js_oneval :: JSVal -> JSString -> IO ()

  
main :: IO ()
main =
  do
    cb <- asyncCallback2 (\ code target ->
      parseAndEval (textFromJSVal code) `catchSome` (pure . pack . displayException)
        >>= js_oneval target)
    js_setup cb
    releaseCallback cb
  where
    catchSome = catch :: IO a -> (SomeException -> IO a) -> IO a
  
    parseAndEval t = runStmts t <&> (\ e -> case e of
      Prim (Number d) -> pack (show d)
      Prim (Text t)   -> textToJSString t
      _               -> error "eval: component not found \"repr\"")
      
