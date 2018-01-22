{-# LANGUAGE OverloadedStrings #-}
module Prim
  ( numberSelf
  , boolSelf
  )
where

import Types.Expr
import qualified Types.Parser as Parser

import qualified Data.Map as M
import qualified Data.IORef
import System.IO( Handle )
import qualified Data.Text.IO as T
import qualified System.IO.Error as IO
import Control.Monad.Trans
--import Control.Monad.Free
import Bound
      
      
-- | Number
numberSelf :: Ord k => Double -> M.Map (Key k) (Node (Key k) (Member (Key k) a))
numberSelf d = M.fromList [
  (Unop Parser.Neg, (Pure . lift . Number) (-d)),
  (Binop Parser.Add, nodebinop (NAdd d)),
  (Binop Parser.Sub, nodebinop (NSub d)),
  (Binop Parser.Prod, nodebinop (NProd d)),
  (Binop Parser.Div, nodebinop (NDiv d)),
  (Binop Parser.Pow, nodebinop (NPow d)),
  (Binop Parser.Gt, nodebinop (NGt d)),
  (Binop Parser.Lt, nodebinop (NLt d)),
  (Binop Parser.Eq, nodebinop (NEq d)),
  (Binop Parser.Ne, nodebinop (NNe d)),
  (Binop Parser.Ge, nodebinop (NGe d)),
  (Binop Parser.Le, nodebinop (NLe d))
  ]

nodebinop x = (Pure . lift . blockList []) [
  (Label "return", (Pure . toE) ((Var . B) (Label "x") `AtPrim` x))
  ]
  
  
-- | Bool
boolSelf :: Ord k => Bool -> M.Map (Key k) (Node (Key k) (Member (Key k) a))
boolSelf b = M.fromList [
  (Label "match", (Pure . Scope . Var . B . Label)
    (if b then "ifTrue" else "ifFalse"))
  ]


-- | ReadLine
handleSelf :: Ord k => Handle -> M.Map (Key k) (Node (Key k) (Member (Key k) a))
handleSelf h = M.fromList [
  (Label "getLine", nodehget (HGetLine h)),
  (Label "getContents", nodehget (HGetContents h)),
  (Label "putStr", nodehput (HPutStr h)),
  (Label "putChar", nodehput (HPutChar h))
  ]
  
  
nodehget x = (Pure . lift . blockList [
  (Pure . lift . blockList [] . pure . (,) (Label "await") . Pure . lift) (blockList [] [])
  ]) [
  (Label "onError", (Pure . toE . Var . F) (B 0)),
  (Label "onSuccess", (Pure . toE . Var . F) (B 0)),
  (Label "await", (Pure . toE) (Var (B Self) `AtPrim` x))
  ]
  
  
nodehput x = (Pure . lift . blockList []) [
  (Label "await", (Pure . toE) (Var (B Self) `AtPrim` x))
  ]
 
 
-- | Mut
mutSelf :: Ord k => Expr k a -> IO (M.Map k (Node k (Member k a)))
mutSelf e = do 
  x <- Data.IORef.newIORef e
  return (M.fromList [
    --(Label "set", (Pure . lift . ioBuiltin) (SetMut x)),
    --(Label "get", (Pure . lift . ioBuiltin) (GetMut x))
    ])
    --where
      --ioBuiltin op = (Block [] . M.singleton (Label "run") . Pure
      --  . Builtin (SetMut x)) (Label "then")

    
    

  