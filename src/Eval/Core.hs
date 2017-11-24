module Eval.Core
  ( eval
  , self
  )
where

import Types.Core

import Data.Maybe
import Control.Applicative( liftA2 )
import Control.Monad( join )
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


eval :: Expr a -> Maybe (Expr a)
eval x@(Number _)     = return x
eval x@(String _)     = return x
eval (Var _)          = Nothing
eval x@(Block _)      = return x
eval (e1 `Concat` e2) = Block <$> self (e1 `Concat` e2)
eval (e `At` x)       = self e >>= instantiateSelf >>= M.lookup x
eval (e `Del` x)      = Block <$> self (e `Del` x)
eval (e1 `Update` e2) = Block <$> self (e1 `Update` e2)
    
    
self :: Expr a -> Maybe (M.Map Tag (Scope Tag Expr a))
self (Number d)       = return M.empty
self (String s)       = return M.empty
self (Var _)          = Nothing
self (Block m)        = return m
self (e1 `Concat` e2) = join (liftA2 mergeDisjoint (self e1) (self e2))
  where
    mergeDisjoint :: Ord k => M.Map k a -> M.Map k a -> Maybe (M.Map k a)
    mergeDisjoint =
      M.mergeA
        M.preserveMissing
        M.preserveMissing
        (M.zipWithAMatched (\ _ _ _ -> Nothing))
        
self (e `At` x)       = eval (e `At` x) >>= self
self (e `Del` x)      = self e >>= toPrivate x
self (e1 `Update` e2) = join (liftA2 mergeSubset (self e1) (self e2))
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
    go m1 m2 = Scope (unscope m2 >>= \ v -> case v of
      B b -> if b == x then unscope m1 else return (B b)
      F a -> return (F a))
      
      