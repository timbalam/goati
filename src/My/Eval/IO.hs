{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Effectful evaluator for my language expressions
module My.Eval.IO
  ( evalIO
  )
where

import My.Types.Expr
import My.Types.Error
import My.Types.Interpreter
import My.Eval (K, toDefns, Comp(..), eval)
import My.Util ((<&>))
import Data.List.NonEmpty (NonEmpty)
import Data.Bifunctor
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Void
import Control.Applicative (liftA2)
import Control.Monad (join, (<=<), ap)
import Control.Monad.Trans
import Control.Exception (IOException, catch)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO (Handle, IOMode, withFile)
import Bound (Scope(..), instantiate)
  
  
-- | Effectful evaluation
evalIO :: Expr K Void -> IO (Expr K Void)
evalIO e = go (eval e)
  where
    go :: Comp (Expr K Void) (Expr K Void) (Expr K Void) -> IO (Expr K Void)
    go (Await (e `AtPrim` p) k) = getIOPrim e p (go . k)
    go (Await _ _)               = pure e
    go (Done e)                  = pure e


-- | Run an IO-performing primitive action. A closed expression is required
--   when saving to mutable variables.
--
--   IOPrim values should only occur inside the hidden 'RunIO' of a
--   promise.
--
--   IOPrim values are evaluated by running the IOPrim action, calling
--   the 'onSuccess' or 'onError' handlers on the attached my expression,
--   then passing the 'RunIO' component of the returned promise to the
--   input continuation.
getIOPrim
  :: forall r. Expr K Void
  -> IOPrimTag (Expr K Void)
  -> (Expr K Void -> IO r)
  -> IO r
getIOPrim e p k = case p of
  -- file io
  OpenFile mode -> iotry
    (withFile
      ((T.unpack . string) (e `At` Key "filename"))
      mode
      (\ h -> ok (handleSelf h)))
        
  HGetLine h -> iotry
    (do
      t <- T.hGetLine h
      ok ((M.singleton (Key "val") . Closed . lift . Prim) (String t)))
        
  HGetContents h -> iotry
    (do
      t <- T.hGetContents h
      ok ((M.singleton (Key "val") . Closed . lift . Prim) (String t)))
    
  HPutStr h -> iotry
    (T.hPutStr h (string (e `At` Key "val")) >> ok M.empty)
    
  NewMut -> iotry
    (do
      err <- newIORef (e `At` Key "val")
      ok (iorefSelf err))
    
  GetMut ref -> iotry
    (do
      v <- readIORef ref
      ok ((M.singleton (Key "val") . Closed . lift) (absurd <$> v)))
  
  SetMut ref -> iotry
    (writeIORef ref (e `At` Key "val") >> ok M.empty)
        
  where
    string a = case a of
      Prim (String t) -> t
      _ -> errorWithoutStackTrace "eval: string type"
      
    iotry :: IO r -> IO r
    iotry x = catch x (\ err ->
      k (skip
        (Key "onError")
        ((M.singleton (Key "err") . Closed . lift . Prim) (IOError err))
        e))
    
    ok :: (forall x . M.Map K (Node K (Scope K (Expr K) x))) -> IO r
    ok defs = k (skip (Key "onSuccess") defs e)
    
    skip
      :: K
      -> (forall x. M.Map K (Node K (Scope K (Expr K) x)))
      -> Expr K a
      -> Expr K a
    skip x defs e = (e `Update` toDefns
      (defs <> (M.singleton (Builtin SkipAsync) 
        . Closed . lift . Block . toDefns)
        (dftCallbacks <> (M.singleton (Key "then")
          . Closed . Scope . skip x defs . Var . B) (Builtin Self)))) `At`x
   
    iorefSelf :: IORef (Expr K Void) -> M.Map K (Node K (Scope K (Expr K) a))
    iorefSelf x = M.fromList [
      (Key "set", member (SetMut x)),
      (Key "get", member (GetMut x))
      ]
      where member = Closed . lift . wrapIOPrim
    

  
-- | Symbol
symbolSelf :: K -> M.Map K (Node K (Scope K (Expr K) a))
symbolSelf k = M.fromList [
  (Key "set", (Closed . Scope) ((Var . B) (Key "target") `Update` (Defns []
    . M.singleton k . Closed . lift . Var . B) (Key "value"))),
  (Key "get", (Closed . Scope) ((Var . B) (Key "target") `At` k))
  ]
  

-- | IO
handleSelf :: Handle -> M.Map K (Node K (Scope K (Expr K) a))
handleSelf h = M.fromList [
  (Key "getLine", member (HGetLine h)),
  (Key "getContents", member (HGetContents h)),
  (Key "putStr", member (HPutStr h))
  ]
  where member = Closed . lift . wrapIOPrim
  
  
-- | 'wrapIOPrim p' wraps a 'IOPrimTag' in a default expression with a 
--   'then' component.
wrapIOPrim
  :: IOPrimTag (Expr K Void) -> Expr K a
wrapIOPrim p = (Block . toDefns)
  (dftCallbacks <> (M.singleton (Key "then") . Closed . Scope)
    ((Var . B) (Builtin Self) `AtPrim` p))
  
  
-- | Wrap a my language IO action in a promise interface that passes
--   dispatches 'onSuccess' and 'onError' continuations to the action.
dftCallbacks :: M.Map K (Node K (Scope K (Expr K) a))
dftCallbacks = M.fromList [
  (Key "onError", (Closed . Scope . Var . B) (Builtin SkipAsync)),
  (Key "onSuccess", (Closed . Scope . Var . B) (Builtin SkipAsync))
  ]