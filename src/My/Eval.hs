{-# LANGUAGE OverloadedStrings #-}

-- | Module for my language evaluator

module My.Eval
  ( getField
  , eval
  , K, Expr
  )
where

import My.Types.Expr
import My.Types.Error
import My.Types.Interpreter
import Data.List.NonEmpty( NonEmpty )
import Data.Bifunctor
import Data.Maybe( fromMaybe )
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IORef
import System.IO( Handle )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified System.IO.Error as IO
import Bound( Scope(..), instantiate )


-- | Evaluate an expression
eval :: Expr K a -> Expr K a
eval (e `At` x)     = getField e x
eval (e `AtPrim` p) = getPrim e p
eval e              = e


getField :: Expr K a -> K -> Expr K a
getField e x = eval (instantiateSelf (self e) M.! x)


self
  :: Expr K a
  -> M.Map K (Node K (Scope K (Expr K) a))
self (Number d)     = numberSelf d
self (String s)     = errorWithoutStackTrace "self: String #unimplemented"
self (Bool b)       = boolSelf b
self (Block (Defns en se))  = (instRec <$>) <$> se where
  en' = (instRec <$>) <$> en
  instRec = instantiate (memberNode . (en' !!)) . getRec
self (e `At` x)     = self (getField e x)
self (e `Fix` k)    = go (S.singleton k) e where
  go s (e `Fix` k) = go (S.insert k s) e
  go s e           = fixFields s (self e)
self (e `AtPrim` p) = self (getPrim e p)
self (e `Update` b) = M.unionWith updateNode (self (Block b)) (self e)
  where    
    updateNode
      :: Ord k
      => Node k (Scope k (Expr k) a)
      -> Node k (Scope k (Expr k) a)
      -> Node k (Scope k (Expr k) a)
    updateNode (Closed a) _ =
      Closed a
      
    updateNode (Open m) (Closed a) =
      (Closed . updateMember a) (toDefns m)
      where
        toDefns
          :: Ord k
          => M.Map k (Node k (Scope k (Expr k) a))
          -> Defns k (Expr k) a
        toDefns = Defns [] . fmap (Rec . lift <$>)

        updateMember
          :: Ord k
          => Scope k (Expr k) a
          -> Defns k (Expr k) a
          -> Scope k (Expr k) a
        updateMember e b = Scope (Update (unscope e) (liftDefns b))
        
        liftDefns
          :: (Ord k, Monad m)
          => Defns k m a -> Defns k m (Var k (m a))
        liftDefns = fmap (return . return)
        
    updateNode (Open ma) (Open mb) =
      Open (M.unionWith updateNode ma mb)
  
  
memberNode :: Ord k => Node k (Scope k (Expr k) a) -> Scope k (Expr k) a
memberNode (Closed a) = a
memberNode (Open m) = (lift . Block . Defns []) ((Rec . lift <$>) <$> m)
        
    
instantiateSelf
  :: (Ord k, Show k) 
  => M.Map k (Node k (Scope k (Expr k) a))
  -> M.Map k (Expr k a)
instantiateSelf se = m
  where
    m = (exprNode . (instantiate (m M.!) <$>)) <$> se
      
      
exprNode :: Ord k => Node k (Expr k a) -> Expr k a
exprNode (Closed e) = e
exprNode (Open m) = (Block . Defns []) ((lift <$>) <$> m)
    
    
fixFields
  :: Ord k
  => S.Set k
  -> M.Map k (Node k (Scope k (Expr k) a))
  -> M.Map k (Node k (Scope k (Expr k) a))
fixFields ks se = retmbrs where
  (fixmbrs, retmbrs) = M.partitionWithKey (\ k _ -> k `S.member` ks) se'
  se' = M.map (substNode (M.map memberNode fixmbrs) <$>) se
     
  substNode
    :: Ord k
    => M.Map k (Scope k (Expr k) a)
    -> Scope k (Expr k) a
    -> Scope k (Expr k) a
  substNode m mbr = wrap (unwrap mbr >>= \ v -> case v of
    B b -> maybe (return v) unwrap (M.lookup b m)
    F a -> return v)
      
  unwrap = unscope
  wrap = Scope
  
  
-- | Primitive number
numberSelf :: Double -> M.Map K (Node K (Scope K (Expr K) a))
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

nodebinop x = (Closed . lift . Block . Defns [] . M.fromList) [
  ((Key . K_) "return", (Closed . toRec) ((Var . B) ((Key . K_) "x") `AtPrim` x))
  ]
  
  
-- | Bool
boolSelf :: Bool -> M.Map K (Node K (Scope K (Expr K) a))
boolSelf b = M.fromList [
  (Unop Not, (Closed . lift. Bool) (not b)),
  ((Key . K_) "match", (Closed . Scope . Var . B . Key . K_)
    (if b then "ifTrue" else "ifFalse"))
  ]


-- | ReadLine
handleSelf :: Handle -> M.Map K (Node K (Scope K (Expr K) a))
handleSelf h = M.fromList [
  ((Key . K_) "getLine", nodehget (HGetLine h)),
  ((Key . K_) "getContents", nodehget (HGetContents h)),
  ((Key . K_) "putStr", nodehput (HPutStr h)),
  ((Key . K_) "putChar", nodehput (HPutChar h))
  ]
  
  
nodehget x = (Closed . lift . Block . Defns [
  (Closed . lift . Block . Defns [] . M.singleton ((Key . K_) "await") . Closed
    . lift . Block) (Defns [] M.empty)
  ] . M.fromList) [
  ((Key . K_) "onError", (Closed . toRec . Var . F) (B 0)),
  ((Key . K_) "onSuccess", (Closed . toRec . Var . F) (B 0))
--  ((Key . K_) "await", (Closed . toRec) (Var (B Self) `AtPrim` x))
  ]
  
  
nodehput x = (Closed . lift . Block . Defns [] . M.fromList) [
--  ((Key . K_) "await", (Closed . toRec) (Var (B Self) `AtPrim` x))
  ]
 
 
-- | Mut
mutSelf :: Ord k => Expr k a -> IO (M.Map k (Node k (Scope k (Expr k) a)))
mutSelf e = do 
  x <- Data.IORef.newIORef e
  return (M.fromList [
    --((Key . K_) "set", (Closed . lift . ioBuiltin) (SetMut x)),
    --((Key . K_) "get", (Closed . lift . ioBuiltin) (GetMut x))
    ])
    --where
      --ioBuiltin op = (Block [] . M.singleton ((Key . K_) "run") . Closed
      --  . Builtin (SetMut x)) ((Key . K_) "then")
   
   
getPrim :: Expr K a -> PrimTag -> Expr K a
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
      (runWithVal (e `At` (Key . K_) "onError") . String . T.pack. show)
      (runWithVal (e `At` (Key . K_) "onSuccess") . String)
      <$> IO.tryIOError f
      
  where
    runWithVal :: Expr K a -> Expr K a -> Expr K a
    runWithVal k v = getField
      (k `Update` (Defns [] . M.fromList) [((Key . K_) "val", Closed (lift v))])
      ((Key . K_) "await")