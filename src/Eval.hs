module Eval
  ( get
  , eval 
  )
where

import Types.Core

import Data.Maybe
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


eval :: Expr a -> Maybe (Expr a)
eval Undef      = Nothing
eval (e `At` x) = get e x
eval e          = return e

  
get :: Expr a -> Tag Id -> Maybe (Expr a)
get e x = self e >>= M.lookup x . instantiateSelf >>= eval
  

data V a = V (M.Map (Tag Id) (Scope (Tag Id) Expr a)) | U
  
selfV :: V a -> Maybe (M.Map (Tag Id) (Scope (Tag Id) Expr a))
selfV (V m) = Just m
selfV U     = Nothing


self :: Expr a -> Maybe (M.Map (Tag Id) (Scope (Tag Id) Expr a))
self = selfV <=< evalV
  
    
evalV :: Expr a -> Maybe (V a)
evalV (Number d)          = Nothing
evalV (String s)          = Nothing
evalV (Var _)             = return U
evalV Undef               = return U
evalV (Block en se)     = (return . V) (M.map (instantiate (en' !!) . getEnscope) se) where
  en' = map (instantiate (en' !!) . getEnscope) en
evalV (e `At` x)          = get e x >>= evalV
evalV (e `Fix` x)         = evalV e >>= \ e -> case e of
  U     -> return U
  V m   -> V <$> fixField x m
evalV (e1 `Update` e2)    = (fmap V . join) (liftA2 mergeSubset (self e1) (self e2)) where
  mergeSubset :: Ord k => M.Map k (Scope (Tag Id) Expr a) -> M.Map k (Scope (Tag Id) Expr a) -> Maybe (M.Map k (Scope (Tag Id) Expr a))
  mergeSubset =
    M.mergeA
      M.preserveMissing
      (M.traverseMissing (\ _ _ -> Nothing))
      (M.zipWithMatched (\ _ _ e2 -> e2))
evalV (e1 `Concat` e2)    = (fmap V . join) (liftA2 mergeDisjoint
  (orempty . selfV <$> evalV e1) (orempty . selfV <$> evalV e2)) where
  orempty = maybe M.empty id

  mergeDisjoint :: Ord k => M.Map k a -> M.Map k a -> Maybe (M.Map k a)
  mergeDisjoint =
    M.mergeA
      M.preserveMissing
      M.preserveMissing
      (M.zipWithAMatched (\ _ _ _ -> Nothing))
        
    
instantiateSelf :: M.Map (Tag Id) (Scope (Tag Id) Expr a) -> M.Map (Tag Id) (Expr a)
instantiateSelf se = m
  where
    m = M.map (instantiate (fromJust . flip M.lookup m)) se
    

fixField :: Tag Id -> M.Map (Tag Id) (Scope (Tag Id) Expr a) -> Maybe (M.Map (Tag Id) (Scope (Tag Id) Expr a))
fixField x se =
  go <$> M.lookup x se
  where 
    go xsc = M.map (substField x xsc) (M.delete x se)
    
    substField :: Monad f => Tag Id -> Scope (Tag Id) f a -> Scope (Tag Id) f a -> Scope (Tag Id) f a
    substField x m1 m2 = Scope (unscope m2 >>= \ v -> case v of
      B b -> if b == x then unscope m1 else return v
      F a -> return v)
      