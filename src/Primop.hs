{-# LANGUAGE OverloadedStrings #-}
module Primop
  ( numberSelf
  , boolSelf
  )
where

import Types.Expr
import qualified Data.Map as M
import qualified Data.IORef
import System.IO( Handle )
import Control.Monad.Trans
import Bound
      
      
-- | Number
numberSelf :: Double -> M.Map Tid (Node (Member a))
numberSelf d = M.fromList [
  (Label "neg", (Closed . lift . Number) (-d)),
  (Label "add", nodebinop (NAdd d)),
  (Label "sub", nodebinop (NSub d)),
  (Label "prod", nodebinop (NProd d)),
  (Label "div", nodebinop (NDiv d)),
  (Label "pow", nodebinop (NPow d)),
  (Label "gt", nodebinop (NGt d)),
  (Label "lt", nodebinop (NLt d)),
  (Label "eq", nodebinop (NEq d)),
  (Label "ne", nodebinop (NNe d)),
  (Label "ge", nodebinop (NGe d)),
  (Label "le", nodebinop (NLe d))
  ]

nodebinop f = (Closed . lift . Block [] . M.singleton (Label "return")
  . Closed . toE . Prim . f . Var . B) (Label "x")
  
  
-- | Bool
boolSelf :: Bool -> M.Map Tid (Node (Member a))
boolSelf b = M.fromList [
  (Label "match", (Closed . Scope . Var . B . Label)
    (if b then "ifTrue" else "ifFalse"))
  ]


-- | ReadLine
handleSelf :: Handle -> M.Map Tid (Node (Member a))
handleSelf h = M.fromList [
  (Label "getLine", nodehget (HGetLine h)),
  (Label "getContents", nodehget (HGetContents h)),
  (Label "putStr", nodehput (HPutStr h)),
  (Label "putChar", nodehput (HPutChar h))
  ]
  
  
nodehget f = (Closed . lift . Block [
  (Closed . lift . Block [] . M.singleton (Label "run") . Closed . lift) (Block [] M.empty)
  ] . M.fromList) [
  (Label "onError", (Closed . toE . Var . F) (B 0)),
  (Label "onSuccess", (Closed . toE . Var . F) (B 0)),
  (Label "run", (Closed . toE . Prim 
    . f ((Var . B) (Label "onError")) . Var . B) (Label "onSuccess"))
  ]
  
  
nodehput f = (Closed . lift . Block [] . M.singleton (Label "run")
  . Closed . toE . Prim . f ((Var . B) (Label "val")) ((Var . B) (Label "onError")) . Var . B) (Label "onSuccess")
 
 
-- | Mut
mutSelf :: Expr a -> IO (M.Map Tid (Node (Member a)))
mutSelf e = do 
  x <- Data.IORef.newIORef e
  return (M.fromList [
    --(Label "set", (Closed . lift . ioBuiltin) (SetMut x)),
    --(Label "get", (Closed . lift . ioBuiltin) (GetMut x))
    ])
    --where
      --ioBuiltin op = (Block [] . M.singleton (Label "run") . Closed
      --  . Builtin (SetMut x)) (Label "then")
  
  


  