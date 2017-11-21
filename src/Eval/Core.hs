module Eval.Core
  ( eval
  , self
  )
where

import Types.Core

import Data.Maybe
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


eval :: Expr a -> Maybe (Expr a)
eval x@(Number _) = return x

eval x@(String _) = return x

eval x@(Bool _) = return x

eval (Var _) = Nothing

eval x@(Block _) = return x

eval (a `Concat` b) =
  Block <$> self (a `Concat` b)
    
eval (a `At` x) =
  do
    a <- self a
    a <- instantiateSelf a
    M.lookup x a
    
eval (a `Del` x) =
  Block <$> self (a `Del` x)
    
eval (a `Update` b) =
  Block <$> self (a `Update` b)
    
    
self :: Expr a -> Maybe (M.Map Tag (Scope Tag Expr a))
self (Number x) =
  return M.empty
  
self (String x) = 
  return M.empty
  
self (Bool x) =
  return M.empty
  
self (Var _) =
  Nothing
  
self (Block m) =
  return m
  
self (a `Concat` b) =
  do
    a <- self a
    b <- self b
    mergeDisjoint a b
  where
    mergeDisjoint :: Ord k => M.Map k a -> M.Map k a -> Maybe (M.Map k a)
    mergeDisjoint =
      M.mergeA
        M.preserveMissing
        M.preserveMissing
        (M.zipWithAMatched (\ _ _ _ -> Nothing))

self (a `At` x) =
  do
    a <- eval (a `At` x)
    self a
    
self (a `Del` x) =
  do
    a <- self a
    toPrivate x a
    
self (a `Update` b) =
  do
    a <- self a
    b <- self b
    mergeSubset a b
  where
    mergeSubset :: Ord k => M.Map k a -> M.Map k a -> Maybe (M.Map k a)
    mergeSubset =
      M.mergeA
        M.preserveMissing
        (M.traverseMissing (\ _ _ -> Nothing))
        (M.zipWithMatched (\ _ _ e -> e))
    
    
    
instantiateSelf :: Monad m => M.Map Tag (Scope Tag Expr a) -> m (M.Map Tag (Expr a))
instantiateSelf m = return self
  where
    self = M.map go m
    
    go = instantiate (fromJust . flip M.lookup self)
    

toPrivate :: Tag -> M.Map Tag (Scope Tag Expr a) -> Maybe (M.Map Tag (Scope Tag Expr a))
toPrivate x m =
  do
    scope <- M.lookup x m
    (return . M.delete x) (M.map (go scope) m)
    
  where
    go :: Scope Tag Expr a -> Scope Tag Expr a -> Scope Tag Expr a
    go e1 e2 = Scope (unscope e2 >>= \ v -> case v of
      B b -> if b == x then unscope e1 else return (B b)
      F a -> return (F a))
      
      