{-# LANGUAGE OverloadedStrings #-}

module My.Builtin
  (builtins)
where

import My.Types.Expr
import My.Eval (K, toDefns)
import My.Eval.IO (wrapIOPrim, handleSelf)
import qualified System.IO
import System.IO (IOMode(..))
import qualified Data.Map as M



builtins :: Monad m => M.Map Ident (ExprT K m a)
builtins = M.fromList [
  ("openFile", openFile ReadWriteMode),
  ("stdout", stdout),
  ("stdin", stdin),
  ("stderr", stderr),
  ("mut", mut)
  ]


openFile :: Monad m => IOMode -> ExprT K m a
openFile m = wrapIOPrim (OpenFile m)


stdin :: Monad m => ExprT K m a
stdin = (block . toDefns) (handleSelf System.IO.stdin)

stdout :: Monad m => ExprT K m a
stdout = (block . toDefns) (handleSelf System.IO.stdout)

stderr :: Monad m => ExprT K m a
stderr = (block . toDefns) (handleSelf System.IO.stderr)


mut :: Monad m => ExprT K m a
mut = wrapIOPrim NewMut
    

  