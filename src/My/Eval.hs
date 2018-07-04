{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.Eval
  ( eval, simplify, Comp, Susp(..), Free(..)
  , K, Expr, toDefns, instantiateDefns, instantiateSelf
  )
where

import My.Types.Expr
import My.Types.Error
import My.Types.Interpreter
import My.Util ((<&>), Susp(..))
import Data.List.NonEmpty (NonEmpty)
import Data.Bifunctor
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Void
import Control.Applicative (liftA2)
import Control.Monad (join, (<=<), ap)
import Control.Monad.Trans
import Control.Monad.Free (Free(..))
import Control.Exception (IOException, catch)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO (Handle, IOMode, withFile)
import Bound (Scope(..), instantiate)

   
type Comp r a = Free (Susp r a)
  
-- | Evaluate an expression
eval :: Expr K a -> Comp (Expr K a) (Expr K a) (Expr K a)
eval (Prim p)       = Prim <$> evalPrim p
eval (w `At` x)     = getComponent w x >>= eval
eval (w `Fix` x)    = eval w <&> (`Fix` x)
eval (w `Update` d) = eval w <&> (`Update` d)
eval (w `AtPrim` p) = eval w >>= \ w' -> Free (Susp (w' `AtPrim` p) eval)
eval e              = pure e


-- | Pure evaluator
simplify :: Expr K a -> Expr K a
simplify e = case eval e of
  Pure e -> e
  Free _ -> e


-- | 'getComponent e x' tries to evaluate 'e' to value form and extracts
--   (without evaluating) the component 'x'. 
getComponent :: Expr K a -> K -> Comp (Expr K a) (Expr K a) (Expr K a)
getComponent e x = getMap x . instantiateSelf <$> self e
  
  
getMap :: (Ord k, Show k) => k -> M.Map k v -> v
getMap k = fromMaybe (error ("eval: not a component: " ++ show k)) . M.lookup k

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
self (Prim p)       = primSelf p
self (Block b)      = pure (instantiateDefns b)
self (e `At` x)     = getComponent e x >>= self
self (e `Fix` k)    = go (S.singleton k) e where
  go s (e `Fix` k)  = go (S.insert k s) e
  go s e            = fixComponents s <$> self e
self (e `Update` b) = liftA2 (M.unionWith updateNode) (pure (instantiateDefns b))
  (self e)
self e              = Free (Susp e self)

    
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
  
  
instantiateDefns :: Ord k => Defns k (Expr k) a -> M.Map k (Node k (Scope k (Expr k) a))
instantiateDefns x = case x of
  Defns en se -> instfun en se
  Browse en se -> instfun en se
  where 
    instfun en se = fmap instRec <$> se
      where
        en'     = map (memberNode . fmap instRec . snd) en
        instRec = instantiate (en' !!) . getRec
  

data Inst k m a = Inst (Int -> m a) (Node k (m a))
  
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
  :: M.Map K (Node K (Scope K (Expr K) a))
  -> M.Map K (Expr K a)
instantiateSelf se = m
  where
    m = exprNode . fmap (instantiate self) <$> se
    self (Builtin Self) = Block (toDefns se)
    self k              = m M.! k
      
      
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
primSelf (Text s)       = errorWithoutStackTrace "self: text #unimplemented"
primSelf (Bool b)       = pure (boolSelf b)
primSelf (IOError e)    = errorWithoutStackTrace "self: ioerror #unimplemented"
primSelf p              = evalPrim p >>= primSelf


evalPrim :: Prim (Expr K a) -> Comp (Expr K a) (Expr K a) (Prim (Expr K a))
evalPrim p = case p of
  -- constants
  Number d        -> pure (Number d)
  Text s          -> pure (Text s)
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

        
-- | Bool
boolSelf :: Bool -> M.Map K (Node K (Scope K (Expr K) a))
boolSelf b = if b then match "ifTrue" else match "ifFalse"
  where
    match = M.singleton (Key (K_ "match")) . Closed . Scope . Var . B . Key . K_

  