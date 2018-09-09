module Web where

import My.Version (myiWebVersion)
import My.Syntax.Interpreter (runFile, browse)
import GHCJS.Foreign.Callback
import GHCJS.Types (JSVal)

foreign import javascript unsafe
  "document.getElementById('runcode').addEventListener('click', $1)"
  js_listen_click :: Callback (JSVal ->  IO()) -> IO ()
  
foreign import javascript unsafe
  "document.getElementById('textcode').value"
  js_text_code :: IO 

  
main :: IO ()
main =
  do
    args <- System.Environment.getArgs
    case args of
      [] -> runRepl
      (file:args) -> runOne (file:|args)
      
      

runRepl :: IO ()
runRepl = --System.Directory.getCurrentDirectory >>=
  browse

    
runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  runFile file >> return ()
