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
eval (e `At` x) = getField e x
eval (Prim p)   = evalPrim p
eval e          = e


-- | 'getField e x' evaluates 'e' to value form, then extracts and evaluates
--   the component 'x'. 
getField :: Expr K a -> K -> Expr K a
getField e x = eval (instantiateSelf (self e) M.! x)

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
self (Prim p)       = primSelf p
self (Block (Defns en se))  = (instRec <$>) <$> se where
  en' = (memberNode . (instRec <$>)) <$> en
  instRec = instantiate (en' !!) . getRec
self (e `At` x)     = self (getField e x)
self (e `Fix` k)    = go (S.singleton k) e where
  go s (e `Fix` k) = go (S.insert k s) e
  go s e           = fixFields s (self e)
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
  
      


primSelf
  :: Prim (Expr K a)
  -> M.Map K (Node K (Scope K (Expr K) a))
primSelf (Number d)     = errorWithoutStackTrace "primSelf: Number #unimplemented"
primSelf (String s)     = errorWithoutStackTrace "primSelf: String #unimplemented"
primSelf (Bool b)       = boolSelf b
primSelf p              = self (evalPrim p)


evalPrim :: Prim (Expr K a) -> Expr K a
evalPrim p = case p of
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
  _               -> Prim p
  where
    bool2bool f a = (Prim . Bool . f) (bool a)
    num2num f a = (Prim . Number . f) (num a)
    num2num2num f a b = (Prim . Number) (num a `f` num b)
    num2num2bool f a b = (Prim . Bool) (num a `f` num b)
  
    bool a = case eval a of 
      Prim (Bool b) -> b
      _ -> errorWithoutStackTrace "evalPrim: bool type"
    
    num a = case eval a of
      Prim (Number d) -> d
      _ -> errorWithoutStackTrace "evalPrim: number type"

  
-- | Bool
boolSelf :: Bool -> M.Map K (Node K (Scope K (Expr K) a))
boolSelf b = M.fromList [
  (Key "match", (Closed . Scope . Var . B . Key)
    (if b then "ifTrue" else "ifFalse"))
  ]


-- | ReadLine
handleSelf :: Handle -> M.Map K (Node K (Scope K (Expr K) a))
handleSelf h = M.fromList [
  (Key "getLine", nodehget (HGetLine h)),
  (Key "getContents", nodehget (HGetContents h)),
  (Key "putStr", nodehput (HPutStr h)),
  (Key "putChar", nodehput (HPutChar h))
  ]
  
  
nodehget x = (Closed . lift . Block . Defns [
  (Closed . lift . Block . Defns [] . M.singleton (Key "await") . Closed
    . lift . Block) (Defns [] M.empty)
  ] . M.fromList) [
  (Key "onError", (Closed . toRec . Var . F) (B 0)),
  (Key "onSuccess", (Closed . toRec . Var . F) (B 0))
--  (Key "await", (Closed . toRec) (Var (B Self) `AtPrim` x))
  ]
  
  
nodehput x = (Closed . lift . Block . Defns [] . M.fromList) [
--  (Key "await", (Closed . toRec) (Var (B Self) `AtPrim` x))
  ]
 
 
-- | Mut
mutSelf :: Ord k => Expr k a -> IO (M.Map k (Node k (Scope k (Expr k) a)))
mutSelf e = do 
  x <- Data.IORef.newIORef e
  return (M.fromList [
    --(Key "set", (Closed . lift . ioBuiltin) (SetMut x)),
    --(Key "get", (Closed . lift . ioBuiltin) (GetMut x))
    ])
    --where
      --ioBuiltin op = (Block [] . M.singleton (Key "run") . Closed
      --  . Builtin (SetMut x)) (Key "then")
    
 
getPrim' :: Expr K a -> PrimTag -> Expr K a 
getPrim' e p = case p of
  HGetLine h -> hgetwith (T.hGetLine h) where
    hgetwith f = either 
      (runWithVal (e `At` Key "onError") . String . T.pack. show)
      (runWithVal (e `At` Key "onSuccess") . String)
      <$> IO.tryIOError f
      
  where
    runWithVal :: Expr K a -> Expr K a -> Expr K a
    runWithVal k v = getField
      (k `Update` (Defns [] . M.fromList) [(Key "val", Closed (lift v))])
      (Key "await")