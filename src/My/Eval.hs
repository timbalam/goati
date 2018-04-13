{-# LANGUAGE OverloadedStrings, RankNTypes #-}

-- | Module for my language evaluator

module My.Eval
  ( getComponent
  , eval
  , K, Expr
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
import Control.Monad (join, (<=<))
import Control.Monad.Trans
import Control.Exception (IOException, catch)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO (Handle, IOMode, withFile)
import qualified Data.Text as T
import qualified Data.Text.IO as T
--import qualified System.IO.Error
import Bound (Scope(..), instantiate)

  
-- | I
data Comp r a b = Done b | Await r (a -> Comp r b)
  deriving Functor

instance Applicative (Comp r a) where
  pure = Done
  
  (<*>) = ap
  
instance Monad (Comp r a) where
  return = pure
  
  Done b    >>= k = k b
  Await r f >>= k = Await r (k <=< f)
  
  
-- | Evaluate an expression
eval :: Expr K a -> Comp (Expr K a) (Maybe (Expr K a)) (Expr K a)
eval (w `At` x)     = getComponent w x >>= eval
eval (w `AtPrim` p) = getPrim w p >>= eval
eval e              = Done e


-- | 'getComponent e x' tries to evaluate 'e' to value form and extracts
--   (without evaluating) the component 'x'. 
getComponent :: Expr K a -> K -> Comp (Expr K a) (Maybe (Expr K a)) (Expr K a)
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
  -> Eval a (M.Map K (Node K (Scope K (Expr K) a)))
self (Prim p)               = primSelf p
self (Var a)                = Comp (Var a) self 
self (Block (Defns en se))  = pure ((instRec <$>) <$> se) where
  en'     = (memberNode . (instRec <$>)) <$> en
  instRec = instantiate (en' !!) . getRec
self (e `At` x)             = getComponent e x >>= self
self (e `Fix` k)            = go (S.singleton k) e where
  go s (e `Fix` k)  = go (S.insert k s) e
  go s e            = fixComponents s <$> self e
self (e `Update` b)         = liftA2 (M.unionWith updateNode) (self (Block b))
  (self e)
self (e `AtPrim` p)         = getPrim e p >>= self
self (IOPrim p e)       = Comp (IOPrim p

    
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
primSelf :: Prim -> Maybe (M.Map K (Node K (Scope K (Expr K) a)))
primSelf (Number d)     = Nothing
primSelf (String s)     = Nothing
primSelf (Bool b)       = Just (boolSelf b)
primSelf (IOError e)    = Nothing


evalPrim :: Prim (Expr K a) -> Eval (Expr K a)
evalPrim p = case p of
  -- pure operations
  Unop Not a      -> bool2bool Not not a
  Unop Neg a      -> num2num Neg negate a
  Binop Add a b   -> num2num2num Add (+) a b
  Binop Sub a b   -> num2num2num Sub (-) a b
  Binop Prod a b  -> num2num2num Prod (*) a b
  Binop Div a b   -> num2num2num Div (/) e
  Binop Pow a b   -> num2num2num Pow (**) e
  Binop Gt a b    -> num2num2bool Gt (>) e
  Binop Lt a b    -> num2num2bool Lt (<) e
  Binop Eq a b    -> num2num2bool Eq (==) e
  Binop Ne a b    -> num2num2bool Ne (/=) e
  Binop Ge a b    -> num2num2bool Ge (>=) e
  Binop Le a b    -> num2num2bool Le (<=) e
  where
    bool2bool f g = bimap (Unop f) (Prim . Bool . g . bool) . eval
    num2num f g e = bimap (Unop f) (Prim . Number . g . num) . eval
    num2num2num f g a b = biliftA2 (Binop f) g' <$> progressPair (eval a) (eval b)
      where g' a b = (Prim . Number) (g (num a) (num b))
    num2num2bool f g a b = biliftA2 (Binop f) g' <$> progressPair (eval a) (eval b)
      where g' a b = (Prim . Bool) (g (num a) (num b))
  
    bool a = case a of 
      Prim (Bool b) -> b
      _ -> errorWithoutStackTrace "eval: bool type"
    
    num a = case a of
      Prim (Number d) -> d
      _ -> errorWithoutStackTrace "eval: number type"
      
    progressPair :: Eval a -> Eval a -> Eval (a, a)
    progressPair (Stuck a) (Stuck b) = Stuck (a, b)
    progressPair (Stuck a) (Complete b) = Stuck (a, b)
    progressPair (Complete a) (Stuck b) = Stuck (a, b)
    progressPair (Complete a) (Complete b) = Complete (a, b)

      
      
      
-- | Effectful evaluation
evalIO :: Expr K a -> IO (Expr K a)
evalIO (IOPrim p e) = getIOPrim p e evalIO
evalIO e = eval e


getIOPrim
  :: IOPrim (Expr K Void)
  -> Expr K a
  -> (Expr K a -> IO (Expr K a))
  -> IO (Expr K a)
getIOPrim p e k = case p of
  -- file io
  OpenFile mode -> iotry
    (withFile
      ((T.unpack . string) (e `At` Key "filename"))
      mode
      (\ h -> ok (handleSelf h)))
        
  HGetLine h -> iotry
    (do t <- T.hGetLine h; ok ((valSelf . Prim) (String t)))
        
  HGetContents h -> iotry
    (do t <- T.hGetContents h; ok ((valSelf . Prim) (String t)))
    
  HPutStr h -> iotry
    (T.hPutStr h (string (e `At` Key "val")) >> done)
    
  NewMut -> iotry
    (do err <- newIORef (e `At` Key "val"); ok (iorefSelf err))
    
  GetMut ref -> iotry
    (do v <- readIORef ref; ok (valSelf v))
  
  SetMut ref -> iotry
    (writeIORef ref (e `At` Key "val") >> done)
    
  p -> pure (fromMaybe (errorWithoutStackTrace "eval: ??") (getPrim e p))
        
  where
    string a = case a of
      Prim (String t) -> t
      _ -> errorWithoutStackTrace "eval: string type"
      
    
    evalAsync :: (forall x . Expr K x -> Expr K x) -> IO (Expr K a)
    evalAsync f = k (skippableAction f e)
      
    done = evalAsync ((`At` RunIO) . (`At` Key "onSuccess"))
    
    ok :: (forall x . M.Map K (Node K (Scope K (Expr K) x))) -> IO (Expr K a)
    ok self = evalAsync (\ e -> 
      ((e `Update` toDefns self) `At` Key "onSuccess") `At` RunIO)
    
    iotry :: IO (Expr K a) -> IO (Expr K a)
    iotry x = catch x (\ e -> err (ioerrorSelf e))
    
    
    err :: (forall x . M.Map K (Node K (Scope K (Expr K) x))) -> IO (Expr K a)
    err self = evalAsync ((`At` RunIO) . (`At` Key "onError")
      . (`Update` toDefns self))
      
      
    ioerrorSelf :: IOException -> M.Map K (Node K (Scope K (Expr K) a))
    ioerrorSelf x = (M.singleton (Key "err") . Closed . lift . Prim) (IOError x)


    valSelf :: Expr K Void -> M.Map K (Node K (Scope K (Expr K) a))
    valSelf v = (M.singleton (Key "val") . Closed . lift) (absurd <$> v)


    iorefSelf :: IORef (Expr K Void) -> M.Map K (Node K (Scope K (Expr K) a))
    iorefSelf x = M.fromList [
      (Key "set", member (SetMut x)),
      (Key "get", member (GetMut x))
      ]
      where member p = (Closed . lift . asyncAction) ((`AtPrim` p) . Var)
    
  
-- | Bool
boolSelf :: Bool -> M.Map K (Node K (Scope K (Expr K) a))
boolSelf b = M.fromList [
  (Key "match", (Closed . Scope . Var . B . Key)
    (if b then "ifTrue" else "ifFalse"))
  ]
  

-- | IO
handleSelf :: Handle -> M.Map K (Node K (Scope K (Expr K) a))
handleSelf h = M.fromList [
  (Key "getLine", member (HGetLine h)),
  (Key "getContents", member (HGetContents h)),
  (Key "putStr", member (HPutStr h))
  ]
  where member p = (Closed . lift . asyncAction) ((`AtPrim` p) . Var)

  
openFile :: IOMode -> Expr K a
openFile m = (wrapAsync . asyncAction) ((`AtPrim` OpenFile m) . Var)


mut :: Expr K a
mut = (wrapAsync . asyncAction) ((`AtPrim` NewMut) . Var)

  
asyncAction :: (Var K (Var Int a) -> Expr K (Var K (Var Int a))) -> Expr K a
asyncAction f = (Block . Defns [] . M.fromList) [
  (Key "run", (Closed . toRec . f . B) (Key "continue"))
  ]
  
    
skippableAction
  :: (forall x . Expr K x -> Expr K x) -> Expr K a -> Expr K a
skippableAction f = f . (`Update` (Defns [] . M.fromList) [
      (SkipIO, (Closed . lift . asyncAction) (skippableAction f . Var))
      ])
  
  
wrapAsync :: Expr K a -> Expr K a
wrapAsync e = (Block . toDefns)
  (dftCallbacks <> M.fromList [
    (Key "then", (Closed . Scope) (wrapAsync dispatch)),
    (RunIO, Closed (lift e))
    ])
  where
    dispatch :: Expr K (Var K a)
    dispatch = (Var (B RunIO) `Update` (Defns []
      . M.fromList) [
        (Key "continue", (Closed . lift) (Var (B Self) `Fix` Key "then"))
        ]) `At` Key "run"
  
  
    dftCallbacks :: M.Map K (Node K (Scope K (Expr K) a))
    dftCallbacks = M.fromList [
      (Key "onError", (Closed . Scope . Var) (B SkipIO)),
      (Key "onSuccess", (Closed . Scope . Var) (B SkipIO))
      ]
  