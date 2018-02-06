{-# LANGUAGE OverloadedStrings #-}
module Eval
  ( getField
  , eval
  )
where

import Types.Expr
import Types.Error

import Data.List.NonEmpty( NonEmpty )
import Data.Bifunctor
import Data.Maybe( fromMaybe )
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
--import qualified Data.Map.Merge.Lazy as M
import qualified Data.Set as S
import qualified Data.IORef
import System.IO( Handle )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified System.IO.Error as IO
import Bound


-- | Evaluate an expression
eval :: Expr a -> Expr a
eval (e `At` x)     = getField e x
eval (e `AtPrim` p) = getPrim e p
eval e              = e


getField :: Expr a -> Key -> Expr a
getField e x = (maybe
  (errorWithoutStackTrace ("get: " ++ show x))
  eval
  . M.lookup x . instantiateSelf) (self e)


self :: Expr a -> M.Map Key (Node (Scope Key Expr a))
self (Number d)     = numberSelf d
self (String s)     = errorWithoutStackTrace "self: String #unimplemented"
self (Bool b)       = boolSelf b
self (Block en se)  = (instRec <$>) <$> se where
  en' = (instRec <$>) <$> en
  instRec = instantiate (memberNode . (en' !!)) . getRec
self (e `At` x)     = self (getField e x)
self (e `Fix` k)    = go (S.singleton k) e where
  go s (e `Fix` k) = go (S.insert k s) e
  go s e           = fixFields s (self e)
self (e `AtPrim` p) = self (getPrim e p)
self (e `Update` w) = M.unionWith updateNode (self w) (self e)
  where    
    updateNode
      :: Node (Scope Key Expr a)
      -> Node (Scope Key Expr a)
      -> Node (Scope Key Expr a)
    updateNode (Closed a) _ =
      Closed a
      
    updateNode (Open m) (Closed a) =
      (Closed . updateMember a . lift) (toBlock m)
      where
        toBlock :: M.Map Key (Node (Scope Key Expr a)) -> Expr a
        toBlock = Block [] . fmap (Rec . lift <$>)

        updateMember :: Scope Key Expr a -> Scope Key Expr a -> Scope Key Expr a
        updateMember e w = wrap (Update (unwrap e) (unwrap w))
        
        unwrap = unscope
        wrap = Scope
        
    updateNode (Open ma) (Open mb) =
      Open (M.unionWith updateNode ma mb)
  
  
memberNode :: Node (Scope Key Expr a) -> Scope Key Expr a
memberNode (Closed a) = a
memberNode (Open m) = (lift . Block []) ((Rec . lift <$>) <$> m)
        
    
instantiateSelf
  :: M.Map Key (Node (Scope Key Expr a))
  -> M.Map Key (Expr a)
instantiateSelf se = m
  where
    m = (exprNode . (instantiate inst <$>)) <$> se
      
    inst k = (fromMaybe . errorWithoutStackTrace) ("get: " ++ show k) (M.lookup k m)
      
      
exprNode :: Node (Expr a) -> Expr a
exprNode (Closed e) = e
exprNode (Open m) = Block [] ((lift <$>) <$> m)
    
    
fixFields
  :: S.Set Key
  -> M.Map Key (Node (Scope Key Expr a))
  -> M.Map Key (Node (Scope Key Expr a))
fixFields ks se = retmbrs where
  (fixmbrs, retmbrs) = M.partitionWithKey (\ k _ -> k `S.member` ks) se'
  se' = M.map (substNode (M.map memberNode fixmbrs) <$>) se
     
  substNode
    :: M.Map Key (Scope Key Expr a)
    -> Scope Key Expr a
    -> Scope Key Expr a
  substNode m mbr = wrap (unwrap mbr >>= \ v -> case v of
    B b -> maybe (return v) unwrap (M.lookup b m)
    F a -> return v)
      
  unwrap = unscope
  wrap = Scope
  
  
-- | Primitive number
numberSelf :: Double -> M.Map Key (Node (Scope Key Expr a))
numberSelf d = M.fromList [
  (Unop Neg, (Closed . lift . Number) (-d)),
  (Binop Add, nodebinop (NAdd d)),
  (Binop Sub, nodebinop (NSub d)),
  (Binop Prod, nodebinop (NProd d)),
  (Binop Div, nodebinop (NDiv d)),
  (Binop Pow, nodebinop (NPow d)),
  (Binop Gt, nodebinop (NGt d)),
  (Binop Lt, nodebinop (NLt d)),
  (Binop Eq, nodebinop (NEq d)),
  (Binop Ne, nodebinop (NNe d)),
  (Binop Ge, nodebinop (NGe d)),
  (Binop Le, nodebinop (NLe d))
  ]

nodebinop x = (Closed . lift . Block [] . M.fromList) [
  (Ident "return", (Closed . toRec) ((Var . B) (Ident "x") `AtPrim` x))
  ]
  
  
-- | Bool
boolSelf :: Bool -> M.Map Key (Node (Scope Key Expr a))
boolSelf b = M.fromList [
  (Unop Not, (Closed . lift. Bool) (not b)),
  (Ident "match", (Closed . Scope . Var . B . Ident)
    (if b then "ifTrue" else "ifFalse"))
  ]


-- | ReadLine
handleSelf :: Handle -> M.Map Key (Node (Scope Key Expr a))
handleSelf h = M.fromList [
  (Ident "getLine", nodehget (HGetLine h)),
  (Ident "getContents", nodehget (HGetContents h)),
  (Ident "putStr", nodehput (HPutStr h)),
  (Ident "putChar", nodehput (HPutChar h))
  ]
  
  
nodehget x = (Closed . lift . Block [
  (Closed . lift . Block [] . M.singleton (Ident "await") . Closed . lift) (Block [] M.empty)
  ] . M.fromList) [
  (Ident "onError", (Closed . toRec . Var . F) (B 0)),
  (Ident "onSuccess", (Closed . toRec . Var . F) (B 0))
--  (Ident "await", (Closed . toRec) (Var (B Self) `AtPrim` x))
  ]
  
  
nodehput x = (Closed . lift . Block [] . M.fromList) [
--  (Ident "await", (Closed . toRec) (Var (B Self) `AtPrim` x))
  ]
 
 
-- | Mut
mutSelf :: Expr a -> IO (M.Map Key (Node (Scope Key Expr a)))
mutSelf e = do 
  x <- Data.IORef.newIORef e
  return (M.fromList [
    --(Ident "set", (Closed . lift . ioBuiltin) (SetMut x)),
    --(Ident "get", (Closed . lift . ioBuiltin) (GetMut x))
    ])
    --where
      --ioBuiltin op = (Block [] . M.singleton (Ident "run") . Closed
      --  . Builtin (SetMut x)) (Ident "then")
   
   
getPrim :: Expr a -> PrimTag -> Expr a
getPrim e x = case x of
  NAdd a -> nwith (a +) e
  NSub a -> nwith (a -) e
  NProd a -> nwith (a *) e
  NDiv a -> nwith (a /) e
  NPow a -> nwith (a **) e
  NEq a -> ncmp (a ==) e
  NNe a -> ncmp (a /=) e
  NLt a -> ncmp (a <) e
  NGt a -> ncmp (a >) e
  NLe a -> ncmp (a <=) e
  NGe a -> ncmp (a >=) e
  _       -> e `AtPrim` x
  where
    nwith f = Number . f . number . eval
    ncmp f = Bool . f . number . eval
    
    number (Number d) = d
    number _          = errorWithoutStackTrace ("get: " ++ show x)
    
    
    
getPrim' e p = case p of
  HGetLine h -> hgetwith (T.hGetLine h) where
    hgetwith f = either 
      (runWithVal (e `At` Ident "onError") . String . T.pack. show)
      (runWithVal (e `At` Ident "onSuccess") . String)
      <$> IO.tryIOError f
      
  where
    runWithVal :: Expr a -> Expr a -> Expr a
    runWithVal k v = getField
      (k `Update` (Block [] . M.fromList) [(Ident "val", Closed (lift v))])
      (Ident "await")