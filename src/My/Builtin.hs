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



builtins :: Monad m => M.Map Ident (Expr K m a)
builtins = M.fromList [
  ("openFile", openFile ReadWriteMode),
  ("stdout", stdout),
  ("stdin", stdin),
  ("stderr", stderr),
  ("mut", mut)
  ]


openFile :: Monad m => IOMode -> Expr K m a
openFile m = wrapIOPrim (OpenFile m)


stdin :: Monad m => Expr K m a
stdin = (Expr . return . Block . toDefns) (handleSelf System.IO.stdin)

stdout :: Monad m => Expr K m a
stdout = (Expr . return . Block . toDefns) (handleSelf System.IO.stdout)

stderr :: Monad m => Expr K m a
stderr = (Expr . return . Block . toDefns) (handleSelf System.IO.stderr)


mut :: Monad m => Expr K m a
mut = wrapIOPrim NewMut
    

  