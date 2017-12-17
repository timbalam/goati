module Eval
  ( get
  , eval 
  )
where

import Types.Expr

import Data.Maybe
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


eval :: Expr a -> Either (EvalError Id a) (Expr a)
eval (v `At` x)  = get v x
eval v           = return v


get :: Expr a -> Tag Id -> Either (EvalError Id a) (Expr a)
get e x = self e >>= maybe (Left (NoField x)) return . (M.lookup x . instantiateSelf >=> runEval) >>= eval


self :: Expr a -> Either (EvalError Id a) (M.Map (Tag Id) (Scope (Tag Id) Eval a))
self (Number d)         = error "eval: Number"
self (String s)         = error "eval: String"
self (Var a)            = Left (UnboundVar a)
self (Block en se)      = return (M.map (instantiate (en' !!) . getEnscope) se) where
  en' = map (instantiate (en' !!) . getEnscope) en
self (v `At` x)          = get v x >>= self
self (v `Fix` x)         = self v >>= fixField x
self (v `Update` w)    = join (liftA2 mergeSubset (self v) (self w)) where
  mergeSubset :: Ord k => M.Map k v -> M.Map k v -> Either (ExprError Id a) (M.Map k v)
  mergeSubset =
    M.mergeA
      M.preserveMissing
      (M.traverseMissing (\ k _ -> Left (NoField k)))
      (M.zipWithMatched (\ _ _ e2 -> e2))
self (v `Concat` e)    = join (liftA2 mergeDisjoint
  (self v) (maybe (return M.empty) self (getEval e))) where
  mergeDisjoint :: Ord k => M.Map k a -> M.Map k a -> Maybe (M.Map k a)
  mergeDisjoint =
    M.mergeA
      M.preserveMissing
      M.preserveMissing
      (M.zipWithAMatched (\ k _ _ -> Left (DuplicateField k)))
        
    
instantiateSelf :: M.Map (Tag Id) (Scope (Tag Id) Eval a) -> M.Map (Tag Id) (Eval a)
instantiateSelf se = m
  where
    m = M.map (instantiate (maybe (Eval Nothing) id . flip M.lookup m)) se
    

fixField :: Tag Id -> M.Map (Tag Id) (Scope (Tag Id) Eval a) -> Either (ExprError Id a) (M.Map (Tag Id) (Scope (Tag Id) Eval a))
fixField x se =
  maybe (Left (NoField x)) (return . go) M.lookup x se
  where 
    go xsc = M.map (substField x xsc) (M.delete x se)
    
    substField :: Monad f => Tag Id -> Scope (Tag Id) f a -> Scope (Tag Id) f a -> Scope (Tag Id) f a
    substField x m1 m2 = Scope (unscope m2 >>= \ v -> case v of
      B b -> if b == x then unscope m1 else return v
      F a -> return v)
      