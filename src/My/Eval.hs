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
eval :: Expr K a -> IO (Expr K a)
eval (e `At` x)     = getComponent e x >>= eval
eval (e `AtPrim` p) = getPrim e p >>= eval
eval e              = pure e


-- | 'evalComponent e x' evaluates 'e' to value form, then extracts (without
--   evaluating) the component 'x'. 
getComponent :: Expr K a -> K -> IO (Expr K a)
getComponent e x = self e >>= (M.! x) . instantiateSelf

-- | 'self' evaluates an expression to self form.
--
--   The self form of a value is the set of recursively defined named
--   components of the value.
--
--   Values in self form are able to merge with other self form values,
--   to introduce new and updated components.
self
  :: Expr K a
  -> IO (M.Map K (Node K (Scope K (Expr K) a)))
self (Prim p)               = pure (primSelf p)
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


evalPrim :: Expr K a -> PrimTag -> IO (Expr K a)
evalPrim e p = case p of
  -- pure operations
  Unop Not    -> bool2bool not e
  Unop Neg    -> num2num negate e
  Binop Add   -> num2num2num (+) e
  Binop Sub   -> num2num2num (-) e
  Binop Prod  -> num2num2num (*) e
  Binop Div   -> num2num2num (/) e
  Binop Pow   -> num2num2num (**) e
  Binop Gt    -> num2num2bool (>) e
  Binop Lt    -> num2num2bool (<) e
  Binop Eq    -> num2num2bool (==) e
  Binop Ne    -> num2num2bool (/=) e
  Binop Ge    -> num2num2bool (>=) e
  Binop Le    -> num2num2bool (<=) e
  
  -- file io
  OpenFile mode -> iotry
    (withFile (string (e `At` Key "filename")) mode (ok . handleSelf))
        
  HGetLine h -> iotry
    (T.HGetLine h >>= ok . valSelf . Prim . String)
        
  HGetContents h -> iotry
    (T.HGetContents h >>= ok . valSelf . Prim . String)
    
  HPutStr h -> iotry
    (T.HPutStr (string (e `At` Key "val")) >> eval (e `At` Key "onSuccess"))
    
  NewIORef -> iotry
    (IO.newIORef (e `At` Key "val") >>= ok . iorefSelf)
    
  GetIORef ref -> iotry
    (IO.readIORef ref >>= ok . valSelf)
  
  SetIORef ref -> iotry
    (IO.writeIORef ref (e `At` Key "val") >> eval (e `At` Key "onSuccess"))
        
  where
    bool2bool f e = (pure . Prim . Bool . f) (bool e)
    num2num f e = (pure . Prim . Number . f) (num e)
    num2num2num f e = (pure . Prim . Number) (num (e `At` Key "lhs") `f`
      num (e `At` Key "rhs"))
    num2num2bool f a b = (pure . Prim . Bool) (num (e `At` Key "lhs") `f`
      num (e `At` Key "rhs"))
  
    bool a = case eval a of 
      Prim (Bool b) -> b
      _ -> errorWithoutStackTrace "eval: bool type"
    
    num a = case eval a of
      Prim (Number d) -> d
      _ -> errorWithoutStackTrace "eval: number type"

    string a = case eval a of
      Prim (String t) -> t
      _ -> errorWithoutStackTrace "eval: string type"
    
    
    ok self = eval ((e `Update` toDefns self) `At` Key "onSuccess")
    
    iotry :: IO (Expr K a) -> IO (Expr K a)
    iotry x = IO.catch x (err . ioerrSelf)
    
    err self = eval ((e `Update` toDefns self) `At` Key "onError")
    
    
    handleSelf :: Handle -> M.Map K (Node K (Scope K (Expr K) a))
    handleSelf h = M.fromList [
      (Key "getLine", member (HGetLine h)),
      (Key "getContents", member (HGetContents h)),
      (Key "putStr", member (HPutStr h))
      ]
      where member = Closed . lift . Block . toDefns . primtagSelf
      
      
    ioerrorSelf :: IOError -> M.Map K (Node K (Scope K (Expr K) a))
    ioerrorSelf x = (M.singleton (Key "err") . Closed . lift . Prim) (IOError x)


    valSelf :: Expr K a -> M.Map K (Node K (Scope K (Expr K) a))
    valSelf v = (M.singleton (Key "val") . Closed) (lift e)


    iorefSelf :: IORef -> M.Map k (Node k (Scope k (Expr k) a))
    iorefSelf x = M.fromList [
      (Key "set", member (SetMut x)),
      (Key "get", member (GetMut x))
      ])
      where member = Closed . lift . Block . toDefns . primtagSelf
    
  
-- | Bool
boolSelf :: Bool -> M.Map K (Node K (Scope K (Expr K) a))
boolSelf b = M.fromList [
  (Key "match", (Closed . Scope . Var . B . Key)
    (if b then "ifTrue" else "ifFalse"))
  ]
  

-- | IO
openFile :: Expr K a
openFile = (wrapAsync . Block . toDefns) (primtagSelf OpenFile)


mut :: Expr K a
mut = (wrapAsync . Block . toDefns) (primtagSelf NewIORef)


primtagSelf :: PrimTag -> M.Map K (Node K (Scope K (Expr K) a))
primtagSelf p = m
  where 
    m = M.fromList [
      (Key "run", (Closed . Scope) ((Var (B "continue") `Update` (Defns []
        . M.fromList) [
          (SkipIO, (Closed . lift) (memberNode m))
          ]) `AtPrim` p))
      ]
  
  
wrapAsync :: Expr K a -> Expr K a
wrapAsync e = (Block . Defns [] . M.fromList) 
  (dftCallbacks <> M.fromList [
    (Key "then", (Closed . toRec) (wrapAsync dispatch),
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
  (Key "onError", (Closed . Scope . Var) (B SkipIO)),
  (Key "onSuccess", (Closed . Scope . Var) (B SkipIO))
  ]
  