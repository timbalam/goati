{-# LANGUAGE OverloadedStrings #-}

module My.Builtins
  (builtins)
where

import My.Types.Expr
import My.Eval (K, toDefns)
import My.Eval.IO (wrapIOPrim, handleSelf)
import qualified System.IO
import System.IO (IOMode(..))
import qualified Data.Map as M



builtins :: M.Map Ident (Expr K a)
builtins = M.fromList [
  ("openFile", openFile ReadWriteMode),
  ("stdout", stdout),
  ("stdin", stdin),
  ("stderr", stderr),
  ("mut", mut)
  ]


openFile :: IOMode -> Expr K a
openFile m = wrapIOPrim (OpenFile m)


stdin :: Expr K a
stdin = (Block . toDefns) (handleSelf System.IO.stdin)

stdout :: Expr K a
stdout = (Block . toDefns) (handleSelf System.IO.stdout)

stderr :: Expr K a
stderr = (Block . toDefns) (handleSelf System.IO.stderr)


mut :: Expr K a
mut = wrapIOPrim NewMut
    

  