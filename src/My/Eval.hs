{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables #-}

-- | Module for my language evaluator
{-# LANGUAGE DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.Eval
  ( eval, simplify, evalIO
  , K, Expr
  , openFile, mut, stdin, stdout, stderr
  )
where

import My.Types.Expr
import My.Types.Error
import My.Types.Interpreter
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
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO (Handle, IOMode, withFile)
import qualified System.IO as IO
import qualified Data.Text as T
import qualified Data.Text.IO as T
--import qualified System.IO.Error
import Bound (Scope(..), instantiate)

  
-- | A computation 'Comp r a b' that can suspend with a message 'r'
--   and be resumed with a value 'a' and finally producing a 'b'
data Comp r a b = Done b | Await r (a -> Comp r a b)
  deriving Functor

instance Applicative (Comp r a) where
  pure = Done
  
  (<*>) = ap
  
instance Monad (Comp r a) where
  return = pure
  
  Done b    >>= k = k b
  Await r f >>= k = Await r (k <=< f)
  
  
-- | Evaluate an expression
eval :: Expr K a -> Comp (Expr K a) (Expr K a) (Expr K a)
eval (w `At` x) = getComponent w x >>= eval
eval (Prim p)   = Prim <$> evalPrim p
eval e          = pure e


-- | Pure evaluator
simplify :: Expr K a -> Expr K a
simplify e = case eval e of
  Done e    -> e
  Await _ _ -> e


-- | 'getComponent e x' tries to evaluate 'e' to value form and extracts
--   (without evaluating) the component 'x'. 
getComponent :: Expr K a -> K -> Comp (Expr K a) (Expr K a) (Expr K a)
getComponent e x = (M.! x) . instantiateSelf <$> self e

-- | 'self' evaluates an expression to self form.
--
--   The self form of a value is the set of recursively defined named
--   components of the value.
--
--   Values in self form are able to merge with other self form values,
--   to introduce new and updated components.
self
  :: Expr K a
  -> Comp (Expr K a) (Expr K a) (M.Map K (Node K (Scope K (Expr K) a)))
self (Prim p)               = primSelf p
self (Var a)                = Await (Var a) self 
self (Block (Defns en se))  = pure ((instRec <$>) <$> se) where
  en'     = (memberNode . (instRec <$>)) <$> en
  instRec = instantiate (en' !!) . getRec
self (e `At` x)             = getComponent e x >>= self
self (e `Fix` k)            = go (S.singleton k) e where
  go s (e `Fix` k)  = go (S.insert k s) e
  go s e            = fixComponents s <$> self e
self (e `Update` b)         = liftA2 (M.unionWith updateNode) (self (Block b))
  (self e)
self (IOPrim p e)           = Await (IOPrim p e) self

    
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
  
  
toDefns
  :: Ord k
  => M.Map k (Node k (Scope k (Expr k) a))
  -> Defns k (Expr k) a
toDefns = Defns [] . fmap (Rec . lift <$>)
  
  
-- | Unwrap a closed node or wrap an open node in a scoped expression
--   suitable for instantiating a 'Scope'.
memberNode :: Ord k => Node k (Scope k (Expr k) a) -> Scope k (Expr k) a
memberNode (Closed a) = a
memberNode (Open m) = (lift . Block) (toDefns m)
        
    
-- | Unroll a layer of the recursively defined components of a self form
--   value.
instantiateSelf
  :: (Ord k, Show k) 
  => M.Map k (Node k (Scope k (Expr k) a))
  -> M.Map k (Expr k a)
instantiateSelf se = m
  where
    m = (exprNode . (instantiate (m M.!) <$>)) <$> se
      
      
-- | Unwrap a closed node or wrap an open node in an expression suitable for
--   instantiating a 'Scope'.
exprNode :: Ord k => Node k (Expr k a) -> Expr k a
exprNode (Closed e) = e
exprNode (Open m) = (Block . Defns []) ((lift <$>) <$> m)
    
    
-- | Fix values of a set of components, as if they were private.
fixComponents
  :: Ord k
  => S.Set k
  -> M.Map k (Node k (Scope k (Expr k) a))
  -> M.Map k (Node k (Scope k (Expr k) a))
fixComponents ks se = retmbrs where
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
  
      

-- | Self forms for primitives
primSelf
  :: Prim (Expr K a)
  -> Comp (Expr K a) (Expr K a) (M.Map K (Node K (Scope K (Expr K) a)))
primSelf (Number d)     = errorWithoutStackTrace "self: number #unimplemented"
primSelf (String s)     = errorWithoutStackTrace "self: string #unimplemented"
primSelf (Bool b)       = pure (boolSelf b)
primSelf (IOError e)    = errorWithoutStackTrace "self: ioerror #unimplemented"
primSelf p              = evalPrim p >>= primSelf


evalPrim :: Prim (Expr K a) -> Comp (Expr K a) (Expr K a) (Prim (Expr K a))
evalPrim p = case p of
  -- constants
  Number d        -> pure (Number d)
  String s        -> pure (String s)
  Bool b          -> pure (Bool b)
  IOError e       -> pure (IOError e)
  
  -- pure operations
  Unop Not a      -> bool2bool not a
  Unop Neg a      -> num2num negate a
  Binop Add a b   -> num2num2num (+) a b
  Binop Sub a b   -> num2num2num (-) a b
  Binop Prod a b  -> num2num2num (*) a b
  Binop Div a b   -> num2num2num (/) a b
  Binop Pow a b   -> num2num2num (**) a b
  Binop Gt a b    -> num2num2bool (>) a b
  Binop Lt a b    -> num2num2bool (<) a b
  Binop Eq a b    -> num2num2bool (==) a b
  Binop Ne a b    -> num2num2bool (/=) a b
  Binop Ge a b    -> num2num2bool (>=) a b
  Binop Le a b    -> num2num2bool (<=) a b
  where
    bool2bool f e = Bool . f . bool <$> eval e
    num2num f e =  Number . f . num <$> eval e
    num2num2num f a b = liftA2 f' (eval a) (eval b)
      where f' a b = (Number) (f (num a) (num b))
    num2num2bool f a b = liftA2 f' (eval a) (eval b)
      where f' a b = (Bool) (f (num a) (num b))
  
    bool a = case a of 
      Prim (Bool b) -> b
      _ -> errorWithoutStackTrace "eval: bool type"
    
    num a = case a of
      Prim (Number d) -> d
      _ -> errorWithoutStackTrace "eval: number type"
      
      
-- | Effectful evaluation
evalIO :: Expr K Void -> IO (Expr K Void)
evalIO e = go (eval e)
  where
    go :: Comp (Expr K Void) (Expr K Void) (Expr K Void) -> IO (Expr K Void)
    go (Await (IOPrim p e) k) = getIOPrim p e (go . k)
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
  :: IOPrim (Expr K Void)
  -> Expr K Void
  -> (Expr K Void -> IO (Expr K Void))
  -> IO (Expr K Void)
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
      
    
    apply :: (forall x . Expr K x -> Expr K x) -> IO (Expr K Void)
    apply f = k (nextAction f e)
    
    iotry :: IO (Expr K Void) -> IO (Expr K Void)
    iotry x = catch x (\ e ->
      apply ((`At` RunIO) . (`At` Key "onError")
        . (`Update` (toDefns . M.singleton (Key "err")
          . Closed . lift . Prim) (IOError e))))
          
    
    ok :: (forall x . Expr K x -> Expr K x) -> IO (Expr K Void)
    ok f = apply (\ e -> (f e `At` Key "onSuccess") `At` RunIO)

    iorefSelf :: IORef (Expr K Void) -> M.Map K (Node K (Scope K (Expr K) a))
    iorefSelf x = M.fromList [
      (Key "set", member (SetMut x)),
      (Key "get", member (GetMut x))
      ]
      where member p = (Closed . lift) (wrapAction (IOPrim p))
    
  
-- | Bool
boolSelf :: Bool -> M.Map K (Node K (Scope K (Expr K) a))
boolSelf b = if b then match "ifTrue" else match "ifFalse"
  where
    match = M.singleton (Key "match") . Closed . Scope . Var . B . Key
  
  
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
  where member p = (Closed . lift) (wrapAction (IOPrim p))

  
openFile :: IOMode -> Expr K a
openFile m = wrapAction (IOPrim (OpenFile m))


stdin :: Expr K a
stdin = (Block . toDefns) (handleSelf IO.stdin)

stdout :: Expr K a
stdout = (Block . toDefns) (handleSelf IO.stdout)

stderr :: Expr K a
stderr = (Block . toDefns) (handleSelf IO.stderr)


mut :: Expr K a
mut = wrapAction (IOPrim NewMut)

  
-- | 'asyncAction f' takes an action 'f' that calls the appropriate handlers
--   given to a promise, and wraps it in in a my language promise.
wrapAction
  :: (forall x . Expr K x -> Expr K x) -> Expr K a
wrapAction f = (wrapAsync . Block . Defns [] . M.singleton (Key "run") . Closed
  . toRec . f . Var . B) (Key "continue")
  
  
-- | 'nextAction f' takes an action 'f' that calls appropriate continuations
--   on its argument, and additionally inserts a skip continuation that will
--   return a trivial promise that defers the action 'f'.
--
--   Only appropriate for pure actions 'f'.
nextAction
  :: (forall x . Expr K x -> Expr K x) -> Expr K a -> Expr K a
nextAction f = f . (`Update` (Defns [] . M.singleton SkipIO . Closed
  . lift) (wrapAction (nextAction f)))
  
  
-- | Wrap a my language IO action in a promise interface that passes
--   dispatches 'onSuccess' and 'onError' continuations to the action.
--
--   The action 'run' component should call the corresponding continuations
--   and provide an additional skip continuation for default continuations
--   (see 'wrapAction' and 'nextAction').
wrapAsync :: Expr K a -> Expr K a
wrapAsync e = (Block . toDefns)
  (dftCallbacks <> M.fromList [
    (Key "then", (Closed . Scope) (wrapAsync dispatch)),
    (RunIO, Closed (lift e))
    ])
  where
    dispatch :: Expr K (Var K a)
    dispatch =
      (Var (B RunIO)
        `Update` (Defns [] . M.singleton (Key "continue") . Closed
          . lift) (Var (B Self) `Fix` Key "then"))
        `At` Key "run"
  
  
    dftCallbacks :: M.Map K (Node K (Scope K (Expr K) a))
    dftCallbacks = M.fromList [
      (Key "onError", (Closed . Scope . Var) (B SkipIO)),
      (Key "onSuccess", (Closed . Scope . Var) (B SkipIO))
      ]
  