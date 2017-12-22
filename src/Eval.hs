module Eval
  ( get
  , eval 
  )
where

import Types.Expr
import Types.Error

import Data.Maybe
import Data.List.NonEmpty( NonEmpty )
import Data.Bifunctor
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


eval :: Expr a -> Either (EvalError Id) (Expr a)
eval (e `At` x) = get e x
eval e          = return e


get :: Expr a -> Tid -> Either (EvalError Id) (Expr a)
get e x = do
  m <- self e
  e <- maybe
    (Left (LookupFailed x))
    (first ParamUndefined)
    (M.lookup x (instantiateSelf m))
  eval e


self :: Expr a -> Either (EvalError Id) (M.Map Tid (Member a))
self (Number d)     = error "self: Number"
self (String s)     = error "self: String"
self (Undef a)      = Left (ParamUndefined a)
self (Block en se)  = return (M.map
  (instantiate (en' !!) . getEnscope)
  se) where
  en' = map (instantiate (en' !!) . getEnscope) en
self (e `At` x)     = get e x >>= self
self (e `Fix` x)    = self e >>= fixField x 
self (e `Update` w) = liftA2 mergeSubset
  (self e)
  (self w)
  >>= first UpdateFieldsMissing . getCollect where
  mergeSubset :: M.Map Tid v -> M.Map Tid v -> Collect (NonEmpty Tid) (M.Map Tid v)
  mergeSubset =
    M.mergeA
      M.preserveMissing
      (M.traverseMissing (\ k _ -> (Collect . Left) (pure k)))
      (M.zipWithMatched (\ _ _ e2 -> e2))
self (e `Concat` w)  = liftA2 mergeDisjoint
  (self e)
  (maybe (return M.empty) self (defined w))
  >>= first ConcatFieldsConflict . getCollect where
  mergeDisjoint :: M.Map Tid a -> M.Map Tid a -> Collect (NonEmpty Tid) (M.Map Tid a)
  mergeDisjoint =
    M.mergeA
      M.preserveMissing
      M.preserveMissing
      (M.zipWithAMatched (\ k _ _ -> (Collect . Left) (pure k)))
      
  defined :: Expr a -> Maybe (Expr a)
  defined (e `Fix` x) = (`Fix` x) <$> defined e
  defined (Undef a)   = Nothing
  defined e           = Just e
        
    
instantiateSelf :: M.Map Tid (Member a) -> M.Map Tid (Expr a)
instantiateSelf se = m
  where
    m = M.map
      (instantiate (\ k ->
        (maybe ((Eval . Left) (Pub k)) id) (M.lookup k m)))
      se
    

fixField :: Tid -> M.Map Tid (Member a) -> Either (EvalError Id) (M.Map Tid (Scope Tid Member a))
fixField x se = maybe
  (Left (LookupFailed x))
  (return . go)
  (M.lookup x se)
  where 
    go xel = M.map (substField x xel) (M.delete x se)
      --xsc = maybe ((lift . Eval) (Left x)) id xel
    
    
    
    substField :: Monad f => Tid -> Scope Tid f a -> Scope Tid f a -> Scope Tid f a
    substField x m1 m2 = Scope (unscope m2 >>= \ v -> case v of
      B b -> if b == x then unscope m1 else return v
      F a -> return v)
      