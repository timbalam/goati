{-# LANGUAGE OverloadedStrings #-}
module Primop
  ( numberSelf
  , boolSelf
  )
where

import Types.Expr
import qualified Data.Map as M
import qualified Data.IORef
import Control.Monad.Trans
import Bound
      
-- | Number
numadd, numsub, numprod, numdiv, numpow, numeq, numne, numlt, numgt,
  numle, numge :: Double -> Expr a -> Expr a
numadd d = Primop . NumberBinop AddNumber d
numsub d = Primop . NumberBinop SubNumber d
numprod d = Primop . NumberBinop ProdNumber d
numdiv d = Primop . NumberBinop DivNumber d
numpow d = Primop . NumberBinop PowNumber d
numeq d = Primop . NumberBinop EqNumber d
numne d = Primop . NumberBinop NeNumber d
numlt d = Primop . NumberBinop LtNumber d
numgt d = Primop . NumberBinop GtNumber d
numle d = Primop . NumberBinop LeNumber d
numge d = Primop . NumberBinop GeNumber d


numberSelf :: Double -> M.Map Tid (Node (Member a))
numberSelf d = M.fromList [
  (Label "neg", (Closed . lift . Number) (-d)),
  (Label "add", toNode (numadd d)),
  (Label "sub", toNode (numsub d)),
  (Label "prod", toNode (numprod d)),
  (Label "div", toNode (numdiv d)),
  (Label "pow", toNode (numpow d)),
  (Label "gt", toNode (numgt d)),
  (Label "lt", toNode (numlt d)),
  (Label "eq", toNode (numeq d)),
  (Label "ne", toNode (numne d)),
  (Label "ge", toNode (numge d)),
  (Label "le", toNode (numle d))
  ]
  where toNode = Closed . lift . binop
  
  
binop f = (Block [] . M.singleton (Label "y") . Closed . toE . f . Var . B) (Label "x")
  
  
-- | Bool
booland, boolor, booleq, boolne, boollt, boolgt, boolle,
  boolge :: Bool -> Expr a -> Expr a
booland b = Primop . BoolBinop AndBool b
boolor b = Primop . BoolBinop OrBool b
booleq b = Primop . BoolBinop EqBool b
boolne b = Primop . BoolBinop NeBool b
boollt b = Primop . BoolBinop LtBool b
boolgt b = Primop . BoolBinop GtBool b
boolle b = Primop . BoolBinop LeBool b
boolge b = Primop . BoolBinop GeBool b


boolSelf :: Bool -> M.Map Tid (Node (Member a))
boolSelf b = M.fromList [
  (Label "not", (Closed . lift . Bool) (not b)),
  (Label "and", toNode (booland b)),
  (Label "or", toNode (boolor b)),
  (Label "match", (Closed . Scope . Var . B . Label)
    (if b then "ifTrue" else "ifFalse"))
  ]
  where toNode = Closed . lift . binop
  
 
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
  
  


  