{-# LANGUAGE OverloadedStrings #-}
module Prim
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
  
  

  
   

evalPrimop :: P (Expr a) -> Expr a
evalPrimop p = case p of
  NAdd a e -> nwith (a +) e
  NSub a e -> nwith (a -) e
  NProd a e -> nwith (a *) e
  NDiv a e -> nwith (a /) e
  NPow a e -> nwith (a **) e
  NEq a e -> ncmp (a ==) e
  NNe a e -> ncmp (a /=) e
  NLt a e -> ncmp (a <) e
  NGt a e -> ncmp (a >) e
  NLe a e -> ncmp (a <=) e
  NGe a e -> ncmp (a >=) e
  _       -> Prim p
  where
    nwith f = Number . f . number . eval
    ncmp f = Bool . f . number . eval
    
    number (Number d) = d
    number _          = error "prim: Number"
    
    
    
execPrimop p = case p of
  HGetLine h su er -> hgetwith (T.hGetLine h) su er
    hgetwith f su er = IO.tryIOError f >>= either
      (run er . IOError)
      (run su' . String) where
        su' = su `Update` (Block [] . M.singleton (Label "onError") . Closed) (lift er)
      
  where
    run :: Expr a -> Expr a -> Expr a
    run k v = getField
      (k `Update` (Block [] . M.singleton (Label "val") . Closed) (lift v)) (Label "run")
    
    

  