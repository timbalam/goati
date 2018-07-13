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
import Data.Functor.Identity (Identity(..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO (Handle, IOMode, withFile)
import Bound (Scope(..), instantiate)

   
type Comp a = Free (Susp a a)

-- | 'getComponent e k' does as much work as necessary to compute the component 'k' of 'e'
-- and returns the component. 
getComponent
  :: (Ord k, Show k)
  => Repr (Tag k) a
  -> Tag k
  -> Comp (Repr (Tag k) a) (Either (Tag k) (Repr (Tag k) a))
getComponent e k = fmap instantiateSelf <$> getDefns e (S.singleton k) 
    
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
    
    
-- | 'getDefns e ks' finds the minimum set of components in 'e' needed to
-- construct all of the components in the set 'ks'.
getDefns
  :: (Ord k, Show k)
  => Repr k a
  -> S.Set k
  -> Comp (Repr k a) (Either k (M.Map k (Scope (Repr k a))))
getDefns  _            ks
  | S.null ks             = return (return M.empty)
getDefns (Repr [])     ks = return (Left ks)
getDefns (Repr (v:vs)) ks = go vs v
  where
    go vs (Prim p)       = goPrim vs p
    go vs (Block b)      = goDefns vs b
    go su (e `At` x)     = getComponent e x >>= either (return . Left) (go su)
    go su (e `Fix` x)
      | x `S.member` ks  = case su of 
        []     -> (return . Left) (pure x)
        (v:su) -> go su v
      | otherwise        = go su e
    go a                 = Free (Susp a go)
    
    goDefns su (Defns en se) =
      instantiateDefns en se' <$> getDefns (Repr su) suks
    where
      ks'  = transDeps ks (seBound <$> se)
      -- dependent fields only
      se'  = M.restrictKeys se ks'
      -- unresolved transitive dependencies to search in super
      suks = foldMap suBound se' <> S.difference ks' (M.keySet se)
      
      seBound = foldMapRec S.singleton mempty mempty
      suBound = foldMapRec mempty (either S.singleton mempty) mempty
      
    
    
instantiateDefns
  :: (Ord k, Monad m)
  => [Rec k m a]
  -> M.Map k (Rec k m a)
  -> M.Map k (Scope k m a)
  -> M.Map k (Scope k m a)  
instantiateDefns en se su = se' <> su where
  se'     = instRec <$> se
  en'     = map instRec en
  instRec = instantiate (either (en' !!) (su M.!)) . getRec
      
   
-- | For a set of values, each with dependent set of values,
-- calculate for a subset of values the complete set of transitively dependent values
transDeps :: Ord k => S.Set k -> M.Map k (S.Set k) -> S.Set k
transDeps s m = fst (go s m)
  where
    go :: S.Set k -> M.Map k (S.Set k) -> (S.Set k, M.Map k (S.Set k))
    go s m = foldr
      (\ a (s, m) -> let (s', m') = go a m in (s <> s', m'))
      (s, M.withoutKeys m s)
      (M.restrictKeys m s)
     
    
    
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

  