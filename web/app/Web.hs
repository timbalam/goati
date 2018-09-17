module Main where

import My.Version (myiWebVersion)
import My.Util ( (<&>) )
import My.Syntax.Interpreter (interpret, Repr(..), Prim(..))
import GHCJS.Foreign.Callback
import GHCJS.Types (JSVal)
import Data.JSString (JSString, pack)
import Data.JSString.Text (textFromJSVal, textToJSString)

foreign import javascript unsafe
  "setup($1)"
  js_setup :: Callback (JSVal -> JSVal -> IO()) -> IO ()
  
foreign import javascript unsafe
  "$1.textContent = $2"
  js_oneval :: JSVal -> JSString -> IO ()

  
main :: IO ()
main =
  do
    cb <- asyncCallback2 (\ target ->
      js_oneval target . textToJSString . interpret . textFromJSVal)
    js_setup cb
    releaseCallback cb
  where
      
