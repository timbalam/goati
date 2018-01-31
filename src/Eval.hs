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


-- Useful alias
type Ex k = Expr M.Map (Key Int k)
type N k = Node M.Map (Key Int k)
type S k = Scope (Key Int k)
type M k = M.Map (Key Int k)

-- | Evaluate an expression
eval :: (Ord k, Show k) => Ex k a -> Ex k a
eval (e `At` x)     = getField e x
eval (e `AtPrim` p) = getPrim e p
eval e              = e


getField :: (Ord k, Show k) => Ex k a -> Key Int k -> Ex k a
getField e x = (maybe
  (errorWithoutStackTrace ("get: " ++ show x))
  eval
  . M.lookup x . instantiateSelf) (self e)


self :: (Ord k, Show k) => Ex k a -> M k (N k (S k (Ex k) a))
self (Number d)     = numberSelf d
self (String s)     = errorWithoutStackTrace "self: String #unimplemented"
self (Bool b)       = boolSelf b
self (Block en se)  = M.map (instE <$>) se where
  en' = map (instE <$>) en
  instE = instantiate (memberNode . (en' !!)) . unE
self (e `At` x)     = self (getField e x)
self (e `Fix` k)    = go (S.singleton k) e where
  go s (e `Fix` k) = go (S.insert k s) e
  go s e           = fixFields s (self e)
self (e `AtPrim` p) = self (getPrim e p)
self (e `Update` w) = M.unionWith updateNode (self e) (self w)
  where    
    updateNode
      :: Ord k
      => Node M.Map k (Scope k (Expr M.Map k) a)
      -> Node M.Map k (Scope k (Expr M.Map k) a)
      -> Node M.Map k (Scope k (Expr M.Map k) a)
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
memberNode (Open m) = (lift . Block []) ((E . lift <$>) <$> m)
        
    
instantiateSelf
  :: (Ord k, Show k, Functor (s k))
  => M.Map k (Node s k (Scope k (Expr s k) a))
  -> M.Map k (Expr s k a)
instantiateSelf se = m
  where
    m = M.map (exprNode . (instantiate inst <$>)) se
      
    inst k = (fromMaybe . errorWithoutStackTrace) ("get: " ++ show k) (M.lookup k m)
      
      
exprNode :: Functor (s k) => Node s k (Expr s k a) -> Expr s k a
exprNode (Closed e) = e
exprNode (Open s) = Block [] ((lift <$>) <$> s)
    
    
fixFields
  :: (Ord k, Functor (s k))
  => S.Set k
  -> M.Map k (Node s k (Scope k (Expr s k) a))
  -> M.Map k (Node s k (Scope k (Expr s k) a))
fixFields ks se = retmbrs where
  (fixmbrs, retmbrs) = M.partitionWithKey (\ k _ -> k `S.member` ks) se'
  se' = M.map (substNode (M.map memberNode fixmbrs) <$>) se
     
  substNode
    :: (Ord k, Functor (s k))
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
  (Label "return", (Closed . toE) ((Var . B) (Label "x") `AtPrim` x))
  ]
  
  
-- | Bool
boolSelf :: Ord k => Bool -> M k (N k (S k (Ex k) a))
boolSelf b = M.fromList [
  (Unop Not, (Closed . lift. Bool) (not b)),
  (Label "match", (Closed . Scope . Var . B . Label)
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
  
  
nodehget x = (Closed . lift . Block [
  (Closed . lift . Block [] . M.singleton (Label "await") . Closed . lift) (Block [] M.empty)
  ] . M.fromList) [
  (Label "onError", (Closed . toE . Var . F) (B 0)),
  (Label "onSuccess", (Closed . toE . Var . F) (B 0)),
  (Label "await", (Closed . toE) (Var (B Self) `AtPrim` x))
  ]
  
  
nodehput x = (Closed . lift . Block [] . M.fromList) [
  (Label "await", (Closed . toE) (Var (B Self) `AtPrim` x))
  ]
 
 
-- | Mut
mutSelf :: Ord k => Ex k a -> IO (M k (N k (S k (Ex k) a)))
mutSelf e = do 
  x <- Data.IORef.newIORef e
  return (M.fromList [
    --(Label "set", (Closed . lift . ioBuiltin) (SetMut x)),
    --(Label "get", (Closed . lift . ioBuiltin) (GetMut x))
    ])
    --where
      --ioBuiltin op = (Block [] . M.singleton (Label "run") . Closed
      --  . Builtin (SetMut x)) (Label "then")
   
   
getPrim :: (Ord k, Show k) => Ex k a -> PrimTag -> Ex k a
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
      (runWithVal (e `At` Label "onError") . String . T.pack. show)
      (runWithVal (e `At` Label "onSuccess") . String)
      <$> IO.tryIOError f
      
  where
    runWithVal :: (Ord k, Show k) => Ex k a -> Ex k a -> Ex k a
    runWithVal k v = getField
      (k `Update` (Block [] . M.fromList) [(Label "val", Closed (lift v))])
      (Label "await")