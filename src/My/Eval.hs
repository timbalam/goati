{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.Eval
  ( eval, simplify, Comp, Susp(..), Free(..)
  , Tag(..), Repr, toDefns, instantiateDefns, instantiateSelf
  )
where

import My.Types.Repr
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
import Data.Functor.Identity (Identity(..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO (Handle, IOMode, withFile)
import Bound (Scope(..), instantiate)

   
type Comp a = Free (Susp a a)
  
-- | Evaluate an expression
eval :: (Ord k, Show k) => Repr (Tag k) a -> Comp (Repr (Tag k) a) (Repr (Tag k) a)
eval a = case a of
  Prim p        -> Prim <$> evalPrim p
  w `At` x      -> getComponent w x >>= eval
  w `Fix` x     -> eval w <&> (`Fix` x)
  w `AtPrim` p  -> do
    w' <- eval w
    Free (Susp (w' `AtPrim` p) eval)
  _             -> pure a


-- | Pure evaluator
simplify :: (Ord k, Show k) => Repr (Tag k) a -> Repr (Tag k) a
simplify e = case eval e of
  Pure e -> e
  Free _ -> e


-- | 'getComponent e x' tries to evaluate 'e' to value form and extracts
--   (without evaluating) the component 'x'. 
getComponent
  :: (Ord k, Show k) => Repr (Tag k) a -> Tag k
  -> Comp (Repr (Tag k) a) (Repr (Tag k) a)
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
  :: (Ord k, Show k)
  => Repr (Tag k) a
  -> Comp (Repr (Tag k) a) (M.Map (Tag k) (Scope (Tag k) (Repr (Tag k)) a))
self a = case a of
  Prim p        -> primSelf p
  Block b       -> instantiateDefns b
  e `At` x      -> getComponent e x >>= self
  e `Fix` k     -> let
    go s a = case a of 
      e `Fix` k -> go (S.insert k s) e
      _         -> fixComponents s <$> self a
    in go (S.singleton k) e
  _             -> Free (Susp a self)
  
  
instantiateDefns
  :: (Ord k, Show k)
  => Defns (Tag k) (Repr (Tag k)) a
  -> Comp (Repr (Tag k) a) (M.Map (Tag k) (Scope (Tag k) (Repr (Tag k)) a))
instantiateDefns (Defns su en se) = update se <$> self su
  where
    update se su = instRec <$> se where
      en'     = map instRec en
      instRec = instantiate (either (en' !!) (su M.!)) . getRec

  
toDefns
  :: Ord k
  => M.Map k (Scope k (Repr k) a)
  -> Defns k (Repr k) a
toDefns = Defns Empty [] . fmap (Rec . lift)
 
    
-- | Unroll a layer of the recursively defined components of a self form
--   value.
instantiateSelf
  :: Ord k
  => M.Map (Tag k) (Scope (Tag k) (Repr (Tag k)) a)
  -> M.Map (Tag k) (Repr (Tag k) a)
instantiateSelf se = m
  where
    m = instantiate self <$> se
    
    self (Builtin Self) = Block (toDefns se)
    self k              = m M.! k
    
    
-- | Fix all component values and hide a subset. Newer fix semantics.
fixComponents
  :: (Ord k, Show k)
  => S.Set (Tag k)
  -> M.Map (Tag k) (Scope (Tag k) (Repr (Tag k)) a)
  -> M.Map (Tag k) (Scope (Tag k) (Repr (Tag k)) a)
fixComponents ks se = lift <$> M.withoutKeys (instantiateSelf se) ks

-- | Fix values of a subset of components, as if they were private.
-- Older semantics.
fixComponents'
  :: Ord k
  => S.Set k
  -> M.Map k (Scope k (Repr k) a)
  -> M.Map k (Scope k (Repr k) a)
fixComponents' ks se = retmbrs where
  (fixmbrs, retmbrs) = M.partitionWithKey (\ k _ -> k `S.member` ks) se'
  se' = substNode fixmbrs <$> se
     
  substNode
    :: Ord k
    => M.Map k (Scope k (Repr k) a)
    -> Scope k (Repr k) a
    -> Scope k (Repr k) a
  substNode m mbr = wrap (unwrap mbr >>= \ v -> case v of
    B b -> maybe (return v) unwrap (M.lookup b m)
    F a -> return v)
      
  unwrap = unscope
  wrap = Scope
  
      

-- | Self forms for primitives
primSelf
  :: (Ord k, Show k)
  => Prim (Repr (Tag k) a)
  -> Comp (Repr (Tag k) a) (M.Map (Tag k) (Scope (Tag k) (Repr (Tag k)) a))
primSelf (Number d)     = errorWithoutStackTrace "self: number #unimplemented"
primSelf (Text s)       = errorWithoutStackTrace "self: text #unimplemented"
primSelf (Bool b)       = pure (boolSelf b)
primSelf (IOError e)    = errorWithoutStackTrace "self: ioerror #unimplemented"
primSelf p              = evalPrim p >>= primSelf


evalPrim
  :: (Ord k, Show k)
  => Prim (Repr (Tag k) a)
  -> Comp (Repr (Tag k) a) (Prim (Repr (Tag k) a))
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
      where f' a b = Number (f (num a) (num b))
    num2num2bool f a b = liftA2 f' (eval a) (eval b)
      where f' a b = Bool (f (num a) (num b))
  
    bool a = case a of 
      Prim (Bool b) -> b
      _ -> errorWithoutStackTrace "eval: bool type"
    
    num a = case a of
      Prim (Number d) -> d
      _ -> errorWithoutStackTrace "eval: number type"

        
-- | Bool
boolSelf :: Bool -> M.Map (Tag k) (Scope (Tag k) (Repr (Tag k)) a)
boolSelf b = if b then match "ifTrue" else match "ifFalse"
  where
    match = M.singleton (Key "match") . Scope . Var . B . Key

  