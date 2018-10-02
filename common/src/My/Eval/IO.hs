{-# LANGUAGE OverloadedStrings #-}

module My.Eval.IO
  where

import My.Types.Eval
import qualified System.IO
import System.IO (IOMode(..))
import qualified Data.Map as M



builtins :: [(Ident, Repr (Dyn Ident) IO)]
builtins = M.fromList [
  ("openFile", openFile ReadWriteMode),
  ("stdout", stdout),
  ("stdin", stdin),
  ("stderr", stderr),
  ("mut", mut)
  ]

openFile :: S.Self k => Res k (Eval (Dyn k) IO)
openFile = S.block_ 
  [ S.self_ "open" S.#= return open ]
  where
    open :: Eval (Dyn k) IO
    open en se = Repr (do
      fname <- getRepr (se S.# "file")
      mode <- getRepr (se S.# "ioMode")

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
    

  