{-# LANGUAGE OverloadedStrings #-}

-- | Module for my language evaluator

module My.Eval
  ( evalComponent
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
eval (e `At` x) = evalComponent e x
eval (Prim p)   = Prim (evalPrim p)
eval e          = e


-- | 'evalComponent e x' evaluates 'e' to value form, then extracts and evaluates
--   the component 'x'. 
evalComponent :: Expr K a -> K -> Expr K a
evalComponent e x = eval (instantiateSelf (self M.empty e) M.! x)

-- | 'self' evaluates an expression to self form.
--
--   The self form of a value is the set of recursively defined named
--   components of the value.
--
--   Values in self form are able to merge with other self form values,
--   to introduce new and updated components.
self
  :: Expr K a
  -> M.Map K (Node K (Scope K (Expr K) a))
  -> M.Map K (Node K (Scope K (Expr K) a))
self m (Prim p)               = primSelf m p
self m (Block (Defns en se))  = M.unionWith updateNode b m where
  b = (instRec <$>) <$> se
  en'     = (memberNode . (instRec <$>)) <$> en
  instRec = instantiate (en' !!) . getRec
self m (e `At` x)             = self m (evalComponent e x)
self m (e `Fix` k)            = go (S.singleton k) e where
  go s (e `Fix` k)  = go (S.insert k s) e
  go s e            = fixComponents s (self m e)
self m (e `Update` b)         = self (self m (Block b)) e

    
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
memberNode (Open m) = (lift . Block . Defns []) ((Rec . lift <$>) <$> m)
        
    
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
  -> M.Map K (Node K (Scope K (Expr K) a))
primSelf (Number d)     = errorWithoutStackTrace "primSelf: Number #unimplemented"
primSelf (String s)     = errorWithoutStackTrace "primSelf: String #unimplemented"
primSelf (Bool b)       = boolSelf b
primSelf (IOError e)    = errorWithoutStackTrace "primSelf: IOError #unimplemented"
primSelf (IOReq req)    = errorWithoutStackTrace "primSelf: IOReq"
primSelf p              = primSelf (evalPrim p)


evalPrim :: Prim (Expr K a) -> Prim b
evalPrim p = case p of
  Number d        -> Number b
  Bool b          -> Bool b
  String s        -> String s
  IOError e       -> IOError e
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
  IOReq req       -> IOReq req
  where
    bool2bool f a = (Bool . f) (bool a)
    num2num f a = (Number . f) (num a)
    num2num2num f a b = (Number) (num a `f` num b)
    num2num2bool f a b = (Bool) (num a `f` num b)
  
    bool a = case eval a of 
      Prim (Bool b) -> b
      _ -> errorWithoutStackTrace "evalPrim: bool type"
    
    num a = case eval a of
      Prim (Number d) -> d
      _ -> errorWithoutStackTrace "evalPrim: number type"
      
      
-- | Evaluate with effects
execIO :: Expr K a -> IO (Expr K a)
execIO (e `At` x) = execIOComponent e x
execIO (Prim p)   = execIOPrim p
execIO e          = return e


execIOComponent :: Expr K a -> K -> IO (Expr K a)
execIOComponent e x = selfIO e >>= (M.! x) . instantiateSelf >>= execIO
      
      
selfIO
  :: Expr K a
  -> IO (M.Map K (Node K (Scope K (Expr K) a)))
selfIO (Prim p)     = primSelfIO p
selfIO (e `At` x)   = execIOComponent e x >>= selfIO
selfIO (e `Fix` k)  = go (S.singleton k) e where
  go s (e `Fix` k)  = go (S.insert k s) e
  go s e            = fixComponents s <$> selfIO e
selfIO (e `Update` b)         = liftA2 (M.unionWith updateNode) (self (Block b))
  (self e)
selfIO e            = pure (self e)
      

primSelfIO :: Prim (Expr K a) -> IO (M.Map K (Node K (Scope K (Expr K) a)))
primSelfIO (IOReq req) = ioreqSelfIO req
primSelfIO p = pure (primSelf p)


ioreqSelfIO :: IOReqType -> IO (M.Map K (Node K (Scope K (Expr K) a)))
ioreqSelfIO req = case req of
  HGetLine h -> either (ioError . IOError) (ioValue . String) <$>
    IO.tryIOError (T.hGetLine h)
  HGetContents h -> either (ioError . IOError) (ioValue . String) <$>
    IO.tryIOError (T.hGetContents h)
  HPutStr h -> either (ioError . IOError) (const ioNone) <$>
    IO.tryIOError (T.hPutStr)
  
  
ioError :: Expr K a -> M.Map K (Node K (Scope K (Expr K) a))
ioError err = m 
  where
    m = M.fromList [
      (Key "run", (Closed . Scope) ((Var (B "continue") `Update` (Defns []
        . M.fromList) [
          (Key "err", Closed (lift err)),
          (SkipIO, (Closed . lift) (memberNode m)
          ]) `At` Key "onError"))
      ]
  
ioValue :: Expr K a -> M.Map K (Node K (Scope K (Expr K) a))
ioValue val = m 
  where 
    m = M.fromList [
      (Key "run", (Closed . Scope) ((Var (B "continue") `Update` (Defns []
        . M.fromList) [
          (Key "val", Closed (lift val)),
          (SkipIO, (Closed . lift) (memberNode m))
          ]) `At` Key "onSuccess"))
      ]
  
ioNone :: M.Map K (Node K (Scope K (Expr K) a))
ioNone = m
  where 
    m = M.fromList [
      (Key "run", (Closed . Scope) ((Var (B "continue") `Update` (Defns []
        . M.fromList) [
          (SkipIO, (Closed . lift) (memberNode m))
          ]) `At` Key "onSuccess"))
      ]
    

  
-- | Bool
boolSelf :: Bool -> M.Map K (Node K (Scope K (Expr K) a))
boolSelf b = M.fromList [
  (Key "match", (Closed . Scope . Var . B . Key)
    (if b then "ifTrue" else "ifFalse"))
  ]


-- | IO
handleSelf :: Handle -> M.Map K (Node K (Scope K (Expr K) a))
handleSelf h = M.fromList [
  (Key "getLine", ioreq (HGetLine h)),
  (Key "getContents", ioreq (HGetContents h)),
  (Key "putStr", ioreq (HPutStr h))
  ]

mutSelf :: IORef -> M.Map k (Node k (Scope k (Expr k) a))
mutSelf x = M.fromList [
  (Key "set", ioreq (SetMut x)),
  (Key "get", ioreq (GetMut x))
  ])

  
ioreq :: IOReqType -> Node K (Scope K (Expr K) a)
ioreq = Closed . lift . promiseWrap . Prim . IOReq
  
  
promiseWrap :: Expr K a -> Expr K a
promiseWrap e = (Block . Defns [] . M.fromList) 
  (dftCallbacks <> M.fromList [
    (Key "then", (Closed . toRec) (promiseWrap dispatch),
    (RunIO, Closed (lift e)),
    ])
  where
    dispatch :: Expr K (Var K a)
    dispatch = (Var (B RunIO) `Update` (Defns []
      . M.fromList) [
        (Key "continue", (Closed . lift) (Var (B Self) `Fix` Key "then"))
        ]) `At` Key "run"
  
  
dftCallbacks :: M.Map K (Node K (Scope K (Expr K) a))
dftCallbacks = M.fromList [
  (Key "onError", (Closed . Scope . Var) (B SkipIO),
  (Key "onSuccess", (Closed . Scope . Var) (B SkipIO))
  ]
  