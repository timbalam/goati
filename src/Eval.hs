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
import qualified Data.Text.IO as T
import qualified System.IO.Error as IO
import Bound


-- Useful alias
type Ex k = Expr M.Map (Key k)
type N k = Node M.Map (Key k)
type S k = Scope (Key k)
type M k = M.Map (Key k)

-- | Evaluate an expression
eval :: Ex k a -> Ex k a
eval (e `At` x)     = getField e x
eval (e `AtPrim` p) = getPrim e p
eval e              = return e


getField :: Ex k a -> Key k -> Ex k a
getField e x = do
  m <- self e
  e <- maybe
    (error ("getField: " ++ show x))
    return
    (M.lookup x (instantiateSelf m))
  eval e


self :: Ord k => Ex k a -> M k (N k (S k (Ex k) a))
self (Number d)     = numberSelf d
self (String s)     = error "self: String"
self (Bool b)       = boolSelf b
self (Block en se)  = M.map (instE <$>) se where
  en' = map (instE <$>) en
  instE = instantiate (memberNode . (en' !!)) . unE
self (e `At` x)     = self (getField e x)
self (e `Fix` k)    = go e (S.singleton k) where
  go (e `Fix` k) s = go e (S.insert k s)
  go e           s = fixFields s <$> self e
self (e `PrimAt` p) = self (getPrim e p)
self (e `Update` w) = M.unionWith updateNode (self e) (self w)
  where    
    updateNode
      :: (Ord k, Functor (s k))
      => Node s k (Scope k (Expr s k) a)
      -> Node s k (Scope k (Expr s k) a)
      -> Node s k (Scope k (Expr s k) a)
    updateNode _ (Closed a) =
      Closed a
      
    updateNode (Closed a) (Open m) =
      (Closed . updateMember a . lift) (toBlock m)
      where
        toBlock :: Functor (s k) => s k (Node s k (Scope k (Expr s k) a)) -> Expr s k a
        toBlock = Block [] . fmap (E . lift <$>)

        updateMember :: Scope k (Expr s k) a -> Scope k (Expr s k) a -> Scope k (Expr s k) a
        updateMember e w = wrap (Update (unwrap e) (unwrap w))
        
        unwrap = unscope
        wrap = Scope
        
    updateNode (Open ma) (Open mb) =
      Open (M.unionWith updateNode ma mb)
  
  
memberNode :: Functor (s k) => Node s k (Scope k (Expr s k) a) -> Scope k (Expr s k) a
memberNode (Closed a) = a
memberNode (Open m) = lift (Block [] (fmap (E . lift <$>) m))
        
    
instantiateSelf
  :: (Ord k, Functor (s k))
  => M.Map k (Node s k (Scope k (Expr s k) a))
  -> M.Map k (Expr s k a)
instantiateSelf se = m
  where
    m = M.map (exprNode . fmap (instantiate inst k)) se
      
    inst k = fromMaybe (error ("instantiateSelf: " ++ show k)) (M.lookup k m)
      
      
exprNode :: Functor (s k) => Node s k (Expr s a) -> Expr s a
exprNode (Closed e) = e
exprNode (Open s) = Block [] (fmap (lift <$>) s)
    
    
fixFields
  :: Functor f
  => S.Set k
  -> M.Map k (f (Scope k (Expr s k) a))
  -> M.Map k (f (Scope k (Expr s k) a))
fixFields ks se = retmbrs where
  (fixmbrs, retmbrs) = M.partitionWithKey (\ k _ -> k `member` ks) se' ks
  se' = M.map (substNode fixmbrs <$>) se
     
  substNode
    :: Ord k
    => M.Map k (Scope k (Expr s k) a)
    -> Scope k (Expr s k) a
    -> Scope k (Expr s k) a
  substNode m mbr = wrap (unwrap mbr >>= \ v -> case v of
    B b -> maybe (return v) unwrap (M.lookup b m)
    F a -> return v)
      
  unwrap = unscope
  wrap = Scope
  
  
-- | Primitive number
numberSelf :: Ord k => Double -> M k (N k (S k (Ex k) a))
numberSelf d = M.fromList [
  (Unop Neg, (Pure . lift . Number) (-d)),
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

nodebinop x = (Pure . lift . blockListMap []) [
  (Label "return", (Pure . toE) ((Var . B) (Label "x") `AtPrim` x))
  ]
  
  
-- | Bool
boolSelf :: Ord k => Bool -> M k (N k (S k (Ex k) a))
boolSelf b = M.fromList [
  (Unop Not, (Pure . lift. Bool) (not b)),
  (Label "match", (Pure . Scope . Var . B . Label)
    (if b then "ifTrue" else "ifFalse"))
  ]


-- | ReadLine
handleSelf :: Ord k => Handle -> M k (N k (S k (Ex k) a))
handleSelf h = M.fromList [
  (Label "getLine", nodehget (HGetLine h)),
  (Label "getContents", nodehget (HGetContents h)),
  (Label "putStr", nodehput (HPutStr h)),
  (Label "putChar", nodehput (HPutChar h))
  ]
  
  
nodehget x = (Pure . lift . blockListMap [
  (Pure . lift . Block [] . M.singleton (Label "await") . Pure . lift) (blockList [] [])
  ]) [
  (Label "onError", (Pure . toE . Var . F) (B 0)),
  (Label "onSuccess", (Pure . toE . Var . F) (B 0)),
  (Label "await", (Pure . toE) (Var (B Self) `AtPrim` x))
  ]
  
  
nodehput x = (Pure . lift . blockListMap []) [
  (Label "await", (Pure . toE) (Var (B Self) `AtPrim` x))
  ]
 
 
-- | Mut
mutSelf :: Ord k => Ex k a -> IO (M k (N k (S k (Ex k) a)))
mutSelf e = do 
  x <- Data.IORef.newIORef e
  return (M.fromList [
    --(Label "set", (Pure . lift . ioBuiltin) (SetMut x)),
    --(Label "get", (Pure . lift . ioBuiltin) (GetMut x))
    ])
    --where
      --ioBuiltin op = (Block [] . M.singleton (Label "run") . Pure
      --  . Builtin (SetMut x)) (Label "then")
   
   
getPrim :: Expr s k a -> PrimTag -> Expr s k a
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
  _       -> e `PrimAt` x
  where
    nwith f = Number . f . number . eval
    ncmp f = Bool . f . number . eval
    
    number (Number d) = d
    number _          = error "prim: Number"
    
    
    
getPrim' e p = case p of
  HGetLine h -> hgetwith (T.hGetLine h) where
    hgetwith f = either 
      (runWithVal (e `At` Label "onError") . IOError)
      (runWithVal (e `At` Label "onSuccess") . String)
      <$> IO.tryIOError f
      
  where
    runWithVal :: Ex k a -> Ex k a -> Ex k a
    runWithVal k v = getField
      (k `Update` blockList [] [(Label "val", Pure (lift v))])
      (Label "await")