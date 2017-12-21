module Eval
  ( get
  , eval 
  )
where

import Types.Expr
import Types.Error

import Data.Maybe
import Data.List.NonEmpty
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


type Errors = NonEmpty (FieldErrors Id)

eval :: Expr a -> Either Errors (Expr a)
eval (v `At` x)  = get v x
eval v           = return v


get :: Eval a -> Tag Id -> Either Errors (Expr a)
get (Eval (Left x)) _ = Left 
get e x = do
  m <- self e
  e <- maybe
    [Left (Missing x)]
    (first undefError . runEval)
    (M.lookup x (instantiateSelf e))
  eval e
  where
  undefError :: Undef a -> EvalError Id a
  undefError (UV a) = UnboundVar a
  undefError (UF x) = Missing x


self :: Val a -> Either Errors (M.Map (Tag Id) (Maybe (Scope (Tag Id) Eval b)))
self (Number d)         = error "self: Number"
self (String s)         = error "self: String"
self (Block en se)      = return ((M.map . fmap)
  (instantiate (en' !!) . getEnscope) se) where
  en' = map (instantiate (en' !!) . getEnscope) en
self (e `At` x)          = get e x >>= self
self (e `Fix` x)         = self v >>= fixField x
self (v `Update` w)    = (join . fmap getCollect)
  (liftA2 mergeSubset (self v) (self w)) where
  mergeSubset :: M.Map (Tag Id) v -> M.Map (Tag Id) v -> Collect [EvalError Id a] (M.Map (Tag Id) v)
  mergeSubset =
    M.mergeA
      M.preserveMissing
      (M.traverseMissing (\ k _ -> (Collect . Left) [Missing k]))
      (M.zipWithMatched (\ _ _ e2 -> e2))
self (v `Concat` e)    = (join . fmap getCollect)
  (liftA2 mergeDisjoint (self v)
    (maybe (return M.empty) self (runEval e))) where
  mergeDisjoint :: M.Map (Tag Id) a -> M.Map (Tag Id) a -> Collect [EvalError Id b] (M.Map (Tag Id) a)
  mergeDisjoint =
    M.mergeA
      M.preserveMissing
      M.preserveMissing
      (M.zipWithAMatched (\ k _ _ -> (Collect . Left) [Overlapped k]))
        
    
instantiateSelf :: M.Map (Tag Id) (Scope (Tag Id) Eval a) -> M.Map (Tag Id) (Eval a)
instantiateSelf se = m
  where
    m = M.map (instantiate (maybe (Eval Nothing) id . flip M.lookup m)) se
    

fixField :: Tag Id -> M.Map (Tag Id) (Scope (Tag Id) Eval a) -> Either [EvalError Id b] (M.Map (Tag Id) (Scope (Tag Id) Eval a))
fixField x se =
  maybe (Left [NoField x]) (return . go) (M.lookup x se)
  where 
    go xsc = M.map (substField x xsc) (M.delete x se)
    
    substField :: Monad f => Tag Id -> Scope (Tag Id) f a -> Scope (Tag Id) f a -> Scope (Tag Id) f a
    substField x m1 m2 = Scope (unscope m2 >>= \ v -> case v of
      B b -> if b == x then unscope m1 else return v
      F a -> return v)
      