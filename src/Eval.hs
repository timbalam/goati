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


type FieldErrors' = NonEmpty (FieldError Id)


eval :: Expr'' a -> Either FieldErrors' (Expr'' a)
eval (Val (e `At` x)) = get e x
eval e                = return e


get :: Eval'' a -> Tag Id -> Either FieldErrors' (Expr'' a)
get e x = do
  m <- self e
  e <- maybe
    ((Left . pure) (Missing x))
    (first (pure . Missing) . runEval)
    (M.lookup x (instantiateSelf m))
  eval e


self :: Eval'' a -> Either FieldErrors' (M.Map (Tag Id) (Elem'' a))
self = either (Left . pure . Missing) selfExpr . runEval where
  selfExpr (Val v)     = selfVal v
  selfExpr (e `Fix` x) = selfExpr e >>= fixField x 
  
  selfVal (Number d)      = error "self: Number"
  selfVal (String s)      = error "self: String"
  selfVal (Block en se)   = return ((M.map . fmap)
    (instantiate (en' !!) . getEnscope) se) where
    en' = map (instantiate (en' !!) . getEnscope) en
  selfVal (e `At` x)      = get e x >>= selfExpr
  selfVal (e `Update` w)  = (join . getCollect . fmap getCollect) (liftA2 mergeSubset
    (Collect (self e))
    (Collect (self w))) where
    mergeSubset :: M.Map (Tag Id) v -> M.Map (Tag Id) v -> Collect FieldErrors' (M.Map (Tag Id) v)
    mergeSubset =
      M.mergeA
        M.preserveMissing
        (M.traverseMissing (\ k _ -> (Collect . Left . pure) (Missing k)))
        (M.zipWithMatched (\ _ _ e2 -> e2))
  selfVal (e `Concat` w)  = (join . getCollect . fmap getCollect) (liftA2 mergeDisjoint
    (Collect (self e))
    (Collect (selfExpr w))) where
    mergeDisjoint :: M.Map (Tag Id) a -> M.Map (Tag Id) a -> Collect FieldErrors' (M.Map (Tag Id) a)
    mergeDisjoint =
      M.mergeA
        M.preserveMissing
        M.preserveMissing
        (M.zipWithAMatched (\ k _ _ -> (Collect . Left . pure) (Overlapped k)))
        
    
instantiateSelf :: M.Map (Tag Id) (Elem'' a) -> M.Map (Tag Id) (Eval'' a)
instantiateSelf se = m
  where
    m = M.mapWithKey (\ k -> maybe
      (Eval (Left k))
      (instantiate (\ k' ->
        (maybe (Eval (Left k')) id) (M.lookup k m))))
      se
    

fixField :: Tag Id -> M.Map (Tag Id) (Elem'' a) -> Either FieldErrors' (M.Map (Tag Id) (Elem'' a))
fixField x se = maybe
  ((Left . pure) (Missing x))
  (return . go)
  (M.lookup x se)
  where 
    go xel = (M.map . fmap) (substField x xsc) (M.delete x se) where
      xsc = maybe ((lift . Eval) (Left x)) id xel
    
    
    
    substField :: Monad f => Tag Id -> Scope (Tag Id) f a -> Scope (Tag Id) f a -> Scope (Tag Id) f a
    substField x m1 m2 = Scope (unscope m2 >>= \ v -> case v of
      B b -> if b == x then unscope m1 else return v
      F a -> return v)
      