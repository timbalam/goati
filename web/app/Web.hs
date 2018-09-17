module Main where

import My.Version (myiWebVersion)
import My.Util ( (<&>) )
import My.Syntax.Interpreter (runStmts, Repr(..), Prim(..))
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
    cb <- asyncCallback2 (\ code target ->
      (js_oneval target
        . either
          (pack . displayError)
          (showStmts . eval)
        . readStmts)
        (textFromJSVal code))
    js_setup cb
    releaseCallback cb
  where
    showStmts e = case e of
      Prim (Number d) -> pack (show d)
      Prim (Text t)   -> textToJSString t
      _               -> error "component not found \"repr\"")
      
