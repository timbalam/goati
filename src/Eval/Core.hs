module Eval.Core
  ( eval
  , self
  )
where

import Types.Core

import Data.Maybe
import Control.Applicative( liftA2 )
import Control.Monad( join )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound
import Bound.Scope
  ( instantiateVars
  , hoistScope )

  
eval :: Expr a -> Maybe (Expr a)
eval (e `At` x) = self e >>= instantiateSelf >>= M.lookup x >>= eval
eval e          = return e
    
    
self :: Expr a -> Maybe (M.Map Tag (Scope () Self a))
self (Number d)       = return M.empty
self (String s)       = return M.empty
self (Var _)          = Nothing
self Undef            = Nothing
self (Block en se)    = return (M.map (instantiate (ven' !!)) se) where
  en' = map (instantiate (en' !!)) en
  ven' = map lift en'
self (e `At` x)       = eval (e `At` x) >>= self
self (e `Del` x)      = self e >>= hideField x
self (e1 `Update` e2) = join (liftA2 mergeSubset (self e1) (self e2))
  where
    mergeSubset :: Ord k => M.Map k (Scope () Self a) -> M.Map k (Scope () Self a) -> Maybe (M.Map k (Scope () Self a))
    mergeSubset =
      M.mergeA
        M.preserveMissing
        (M.traverseMissing (\ _ _ -> Nothing))
        (M.zipWithMatched (\ _ e1 e2 -> lift (instantiate1 (instantiate1 emptySelf e1) e2)))
self (e1 `Concat` e2) = join (liftA2 mergeDisjoint (self e1) (self e2))
  where
    mergeDisjoint :: Ord k => M.Map k a -> M.Map k a -> Maybe (M.Map k a)
    mergeDisjoint =
      M.mergeA
        M.preserveMissing
        M.preserveMissing
        (M.zipWithAMatched (\ _ _ _ -> Nothing))
        
    
    
instantiateSelf :: Monad f => M.Map Tag (Scope () Self a) -> f (M.Map Tag (Expr a))
instantiateSelf se = return m
  where
    m = M.map (inst . instantiate1 emptySelf) se
    inst = instantiate (fromJust . flip M.lookup m)
    
    
emptySelf :: Self a
emptySelf = lift (Block [] M.empty)
    

hideField :: Tag -> M.Map Tag (Scope () Self a) -> Maybe (M.Map Tag (Scope () Self a))
hideField x m =
  do
    scope <- M.lookup x m
    let self = instantiate1 emptySelf scope
    (return . M.delete x) (M.map (mapSelf (substField x self)) m)
    
  where
    mapSelf :: (Self a -> Self a) -> Scope () Self a -> Scope () Self a
    mapSelf f = Scope . (fmap . fmap) f . unscope
  
    substField :: Tag -> Self a -> Self a -> Self a
    substField x m1 m2 = Scope (unscope m2 >>= \ v -> case v of
      B b -> if b == x then unscope m1 else return v
      F a -> return v)
      
      