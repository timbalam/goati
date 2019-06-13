module Main where

import Goat.Version (myiWebVersion)
import Goat.Util ((<&>))
import Goat.Interpret.Inspect (inspect)
import GHCJS.Foreign.Callback
  (Callback, asyncCallback3, releaseCallback)
import GHCJS.Types (JSVal)
import GHCJS.Marshal.Pure (pFromJSVal)
import Data.JSString (JSString, pack, unpack)
import Data.JSString.Text
  (textFromJSVal, textToJSString)

foreign import javascript unsafe
  "setup($1)"
  js_setup
   :: Callback (JSVal -> JSVal -> JSVal -> IO())
   -> IO ()
  
foreign import javascript unsafe
  "$1.textContent = $2"
  js_oneval
   :: JSVal -> JSString -> IO ()

  
main :: IO ()
main
  = do
    cb
     <- asyncCallback3
          (\ target name input
           -> js_oneval
                target
                (textToJSString
                  (inspect
                    (unpack (pFromJSVal name))
                    (textFromJSVal input))))
    js_setup cb
    releaseCallback cb
