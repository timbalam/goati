{-# LANGUAGE OverloadedStrings #-}

module My.Base
  (defaultBase)
where

import My.Types.Expr
import My.Eval (K, wrapAction, handleSelf, toDefns)
import qualified System.IO
import System.IO (IOMode(..))
import qualified Data.Map as M



defaultBase :: Ident -> Maybe (Expr K a)
defaultBase i = (M.lookup i . M.fromList) [
  ("openFile", openFile ReadWriteMode),
  ("stdout", stdout),
  ("stdin", stdin),
  ("stderr", stderr),
  ("mut", mut)
  ]


openFile :: IOMode -> Expr K a
openFile m = wrapAction (IOPrim (OpenFile m))


stdin :: Expr K a
stdin = (Block . toDefns) (handleSelf System.IO.stdin)

stdout :: Expr K a
stdout = (Block . toDefns) (handleSelf System.IO.stdout)

stderr :: Expr K a
stderr = (Block . toDefns) (handleSelf System.IO.stderr)


mut :: Expr K a
mut = wrapAction (IOPrim NewMut)
    

  