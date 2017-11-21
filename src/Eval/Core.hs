{-# LANGUAGE OverloadedStrings #-}

module Eval.Core
  ( eval
  , self
  )
where

import Types.Core

import qualified Data.Map as M
import qualified Data.Map.Merge as M
import Bound


eval :: Expr a -> Maybe (Expr a)
eval x@(Number _) = Just x

eval x@(String _) = Just x

eval x@(Bool _) = Just x

eval (Var _) = Nothing

eval x@(Block _) = Just x

eval (a `Concat` b) =
  Block <$> self (a `Concat` b)
    
eval (a `At` x) =
  do
    a <- self a
    instantiateSelf a
    M.lookup x a
    
eval (a `Del` x) =
  Block <$> self (a `Del` x)
    
eval (a `Update` b) =
  Block <$> self (a `Update` b)
    
    
self :: Expr a -> Maybe (Map Tag (Scope Tag Expr a))
self (Number x) =
  Just M.mempty
  
self (String x) = 
  Just M.empty
  
self (Bool x) =
  Just M.empty
  
self (Var _) =
  Nothing
  
self (Block m) =
  Just m
  
self (a `Concat` b) =
  do
    a <- self a
    b <- self b
    mergeDisjoint a b
  where
    mergeDisjoint :: M.Map k a -> M.Map k a -> Maybe (M.Map k a)
    mergeDisjoint =
      M.mergeA
        preserveMissing
        preserveMissing
        zipWithAMatched (\ _ _ _ -> Nothing)

self (a `At` x) =
  do
    a <- eval (a `At` x)
    self a
    
self (a `Del` x) =
  do
    a <- self
    toPrivate x a
    
self (a `Update` b) =
  do
    a <- self a
    b <- self b
    mergeSubset a b
  where
    mergeSubset :: M.Map Tag (Scope Tag Expr a) -> M.Map k (Scope Tag Expr a) -> Maybe (M.Map Tag (Scope Tag Expr a))
    mergeSubset =
      M.mergeA
        preserveMissing
        traverseMissing (\ _ _ -> Nothing)
        zipWithMatched (\ _ _ e -> e)
    
    
    
instantiateSelf :: M.Map Tag (Scope Tag Expr a) -> Maybe (M.Map Tag (Expr a))
instantiateSelf m = return self
  where
    self = map go m
    
    go = instantiate (fromJust . flip M.lookup self)
    

toPrivate :: Tag -> M.Map Tag (Scope Tag Expr a) -> Maybe (M.Map Tag (Scope Tag Expr a))
toPrivate x m =
  do
    scope <- M.lookup x m
    (return . M.delete x) (map (go scope) m)
    
  where
    go :: Scope Tag Expr a -> Scope Tag Expr a -> Scope Tag Expr a
    go e1 e2 = Scope (unscope e2 >>= \ v -> case v of
      B b -> if b == x then unscope e1 else (return . F . return) (B b)
      F a -> F . return <$> a)
      
      