{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Effectful evaluator for my language expressions
module My.Eval.IO
  ( evalIO
  , wrapIOPrim
  , handleSelf
  )
where

import My.Types.Repr
import My.Types.Error
import My.Types.Interpreter (K)
import My.Eval (toDefns, Comp, Susp(..) , Free(..), eval)
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
import Data.Functor.Identity (Identity(..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO (Handle, IOMode, withFile)
import Bound (Scope(..), instantiate)


-- | Effectful evaluation
evalIO 
  :: Repr K Void -> IO ()
evalIO = run . go . eval
  where
    run :: Comp (Repr K Void) (IO ()) -> IO ()
    run (Pure e) = e
    run (Free s) = errorWithoutStackTrace ("evalIO: unhandled " ++ show (yield s))
    
    go
      :: Comp (Repr K Void) (Repr K Void)
      -> Comp (Repr K Void) (IO ())
    go (Free (Susp (e `AtPrim` p) k)) = getIOPrim e p (run . go . k)
    go e                              = const (return ()) <$> e


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
  :: forall r . Repr K Void
  -> IOPrimTag (Repr K Void)
  -> (Repr K Void -> IO r)
  -> Comp (Repr K Void) (IO r)
getIOPrim e p k = case p of
  -- file io
  OpenFile mode ->
    open . T.unpack . text <$> eval (e `At` Key "filename")
    where
      open :: FilePath -> IO r
      open f = iotry (withFile f mode (\ h -> ok (handleSelf h)))
        
  HGetLine h -> (pure . iotry)
    (do
      t <- T.hGetLine h
      ok ((M.singleton (Key "val") . lift . Prim) (Text t)))
        
  HGetContents h -> (pure . iotry)
    (do
      t <- T.hGetContents h
      ok ((M.singleton (Key "val") . lift . Prim) (Text t)))
    
  HPutStr h -> put . text <$> eval  (e `At` Key "val")
    where
      put s = iotry (T.hPutStr h s >> ok M.empty)
    
  NewMut -> (pure . iotry)
    (do
      err <- newIORef (e `At` Key "val")
      ok (iorefSelf err))
    
  GetMut ref -> (pure . iotry)
    (do
      v <- readIORef ref
      ok ((M.singleton (Key "val") . lift) (absurd <$> v)))
  
  SetMut ref -> (pure . iotry)
    (writeIORef ref (e `At` Key "val") >> ok M.empty)
        
  where
    text a = case a of
      Prim (Text t) -> t
      _ -> errorWithoutStackTrace "eval: text type"
      
    iotry :: IO r -> IO r
    iotry x = catch x (\ err ->
      k (skip
        (Key "onError")
        ((M.singleton (Key "err") . lift . Prim) (IOError err))
        e))
    
    ok
      :: (forall x . M.Map K (Scope K (Repr K) x))
      -> IO r
    ok defs = k (skip (Key "onSuccess") defs e)
    
    skip
      :: K
      -> (forall x. M.Map K (Scope K (Repr K) x))
      -> Repr K a
      -> Repr K a
    skip x defs e =  ((((Block . Defns e [] . fmap (Rec . lift))
      (defs <> (M.singleton (Builtin SkipAsync) 
        . lift . Block . toDefns)
        (dftCallbacks <> (M.singleton (Key "then")
          . Scope . skip x defs . Var . B) (Builtin Self))))
            `At` x) `At` Key "then")
   
    iorefSelf :: IORef (Repr K Void) -> M.Map K (Scope K (Repr K) a)
    iorefSelf x = M.fromList [
      (Key "set", member (SetMut x)),
      (Key "get", member (GetMut x))
      ]
      where member = lift . wrapIOPrim
    

  
-- | Symbol
symbolSelf :: K -> M.Map K (Scope K (Repr K) a)
symbolSelf k = M.fromList [
  (Key "set", (Scope . Block . Defns ((return . B) (Key "target")) [] . M.singleton k . return . B) (Key "value")),
  (Key "get", Scope ((Var . B) (Key "target") `At` k))
  ]
  

-- | IO
handleSelf :: Handle -> M.Map K (Scope K (Repr K) a)
handleSelf h = M.fromList [
  (Key "getLine", member (HGetLine h)),
  (Key "getContents", member (HGetContents h)),
  (Key "putStr", member (HPutStr h))
  ]
  where member = lift . wrapIOPrim
  
  
-- | 'wrapIOPrim p' wraps a 'IOPrimTag' in a default expression with a 
--   'then' component.
wrapIOPrim
  :: IOPrimTag (Repr K Void) -> Repr K a
wrapIOPrim p = (Block . toDefns)
  (dftCallbacks <> (M.singleton (Key "then") . Scope)
    ((Var . B) (Builtin Self) `AtPrim` p))
  
  
-- | Wrap a my language IO action in a promise interface that passes
--   dispatches 'onSuccess' and 'onError' continuations to the action.
dftCallbacks :: M.Map K (Scope K (Repr K) a)
dftCallbacks = M.fromList [
  (Key "onError",
    (Scope . Block . Defns Empty []
      . M.singleton (Key "then") . lift . Var . B) (Builtin SkipAsync)),
  (Key "onSuccess",
    (Scope . Block . Defns Empty []
      . M.singleton (Key "then") . lift . Var . B) (Builtin SkipAsync))
  ]