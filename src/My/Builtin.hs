{-# LANGUAGE OverloadedStrings #-}

module My.Builtin
  (builtins)
where

import My.Types.Repr
import My.Eval (K, toDefns)
import My.Eval.IO (wrapIOPrim, handleSelf)
import qualified System.IO
import System.IO (IOMode(..))
import qualified Data.Map as M



builtins :: M.Map Ident (Repr K a)
builtins = M.fromList [
  ("openFile", openFile ReadWriteMode),
  ("stdout", stdout),
  ("stdin", stdin),
  ("stderr", stderr),
  ("mut", mut)
  ]


openFile :: IOMode -> Repr K a
openFile m = wrapIOPrim (OpenFile m)


stdin :: Repr K a
stdin = (Block . toDefns) (handleSelf System.IO.stdin)

stdout :: Repr K a
stdout = (Block . toDefns) (handleSelf System.IO.stdout)

stderr :: Repr K a
stderr = (Block . toDefns) (handleSelf System.IO.stderr)


mut :: Repr K a
mut = wrapIOPrim NewMut
    

  