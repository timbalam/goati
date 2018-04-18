{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.IOPrim
  ( 
  )
where

import My.Types.Expr
import My.Types.Error
import My.Types.Interpreter
import My.Types.IOPrim
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
evalIO :: IOExpr K -> IO (IOExpr K)
evalIO e = go (eval e)
  where
    go :: Comp (IOExpr K) (IOExpr K) (IOExpr K) -> IO (IOExpr K)
    go (Await (Var (IOPrim p e)) k) = getIOPrim p e (go . k)
    go (Await _ _)            = pure e
    go (Done e)               = pure e


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
  :: IOPrim (IOExpr K)
  -> IOExpr K
  -> (IOExpr K -> IO r)
  -> IO r
getIOPrim p e k = case p of
  -- file io
  OpenFile mode -> iotry
    (withFile
      ((T.unpack . string) (e `At` Key "filename"))
      mode
      (\ h -> ok (`Update` toDefns (handleSelf h))))
        
  HGetLine h -> iotry
    (do
      t <- T.hGetLine h
      ok (`Update` (Defns [] . M.singleton (Key "val")
        . Closed . lift . Prim) (String t)))
        
  HGetContents h -> iotry
    (do
      t <- T.hGetContents h
      ok (`Update` (Defns [] . M.singleton (Key "val")
        . Closed . lift . Prim) (String t)))
    
  HPutStr h -> iotry
    (T.hPutStr h (string (e `At` Key "val")) >> ok id)
    
  NewMut -> iotry
    (do
      err <- newIORef (e `At` Key "val")
      ok (`Update` toDefns (iorefSelf err)))
    
  GetMut ref -> iotry
    (do
      v <- readIORef ref
      ok (`Update` (Defns [] . M.singleton (Key "val")
        . Closed . lift) (absurd <$> v)))
  
  SetMut ref -> iotry
    (writeIORef ref (e `At` Key "val") >> ok id)
        
  where
    string a = case a of
      Prim (String t) -> t
      _ -> errorWithoutStackTrace "eval: string type"
      
    
    iotry :: IO (Expr K Void) -> IO (Expr K Void)
    iotry x = catch x (\ err ->
      (k . (`At` Builtin RunIO) .  (`At` Key "onError")
        . (`Update` (toDefns . M.singleton (Key "err")
          . Closed . lift . Prim) (IOError err))) e)
        
    
    ok :: (forall x . Expr K x -> Expr K x) -> IO (Expr K Void)
    ok f = k (f e `At` Key "onSuccess" `At` Builtin RunIO)
    
    
    skip
      :: (forall x . Expr K x -> Expr K x)
      -> (forall x . Expr K x -> Expr K x)
      -> Expr K a -> Expr K a
    skip f g e = f (g e `Update` (Defns [] . M.singleton (Builtin SkipIO) . Closed
      . toRec . skip f g . Var . B) (Builtin NextIO))

    iorefSelf :: IORef (Expr K Void) -> M.Map K (Node K (Scope K (Expr K) a))
    iorefSelf x = M.fromList [
      (Key "set", member (SetMut x)),
      (Key "get", member (GetMut x))
      ]
      where member p = (Closed . lift . wrapAction . Var) (IOPrim p)
    

  
-- | Symbol
symbolSelf :: K -> M.Map K (Node K (Scope K (Expr K) a))
symbolSelf k = M.fromList [
  (Key "set", (Closed . Scope) ((Var . B) (Key "target") `Update` (Defns []
    . M.singleton k . Closed . lift . Var . B) (Key "value"))),
  (Key "get", (Closed . Scope) ((Var . B) (Key "target") `At` k))
  ]
  

-- | IO
handleSelf :: Handle -> M.Map K (Node K (Scope K (Expr K) (IOPrim K)))
handleSelf h = M.fromList [
  (Key "getLine", member (HGetLine h)),
  (Key "getContents", member (HGetContents h)),
  (Key "putStr", member (HPutStr h))
  ]
  where member p = (Closed . lift . wrapAction) (Var . IOPrim p)
  
  
-- | 'wrapAction f' takes an action 'f' that calls the appropriate handlers
--   given to a promise, and wraps it in in a my language promise.
wrapAction
  :: (forall x . Expr K ( -> Expr K x) -> Expr K a
wrapAction f = (promise . Block . Defns [] . M.singleton (Key "run") . Closed
  . toRec . f . Var . B) (Key "continue")
  
  
-- | Wrap a my language IO action in a promise interface that passes
--   dispatches 'onSuccess' and 'onError' continuations to the action.
--
--   The action 'run' component should call the corresponding continuations
--   and provide an additional skip continuation for default continuations
--   (see 'wrapAction' and 'nextAction').
promise :: Expr K a -> Expr K a
promise e = (Block . toDefns)
  (dftCallbacks <> M.fromList [
    (Key "then", (Closed . Scope) undefined),
 --     promise (dispatch (Var (B RunIO)) (Var (B Self)))),
    (Builtin RunIO, Closed (lift e))
    ])
  where
    dispatch :: Expr K a -> Expr K a -> Expr K a
    dispatch prev self = (Block . Defns [
      Closed (lift prev),
      Closed (lift self),
      (Closed . toRec) ((Var . F) (B 1) `Update` (Defns [] 
        . M.singleton (Builtin NextIO) . Closed . lift . Var . B) (Key "continue"))
      ]
      . M.singleton (Key "run") . Closed . toRec) ((
        (Var . F) (B 0) `Update`
          (Defns [] . M.singleton (Key "continue")
            . Closed . lift . Var . F) (B 2))
              `At` Key "run")
        
  
  
    dftCallbacks :: M.Map K (Node K (Scope K (Expr K) a))
    dftCallbacks = M.fromList [
      (Key "onError", (Closed . Scope . Var . B) (Builtin SkipIO)),
      (Key "onSuccess", (Closed . Scope . Var . B) (Builtin SkipIO))
      ]