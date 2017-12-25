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
    return
    (M.lookup x (instantiateSelf m))
  eval e


self :: Expr a -> Either (EvalError Id) (M.Map Tid (Node (Member a)))
self (Number d)     = error "self: Number"
self (String s)     = error "self: String"
self (Undef a)      = Left (ParamUndefined a)
self (Block en se)  = return ((M.map . fmap)
  (instantiate (memberNode . (en' !!)))
  se) where
  en' = (map . fmap) (instantiate (memberNode . (en' !!))) en
self (e `At` x)     = get e x >>= self
self (e `Fix` x)    = self e >>= fixField x 
self (e `Update` w) = liftA2 (M.unionWith updateNode) (self e)
  (self w) where    
  updateNode :: Node (Member a) -> Node (Member a) -> Node (Member a)
  updateNode _            (Closed a)  = Closed a
  updateNode (Closed a)   (Open m)    = (Closed . updateMember a
    . Member . lift) (toBlock m) where
    toBlock :: M.Map Tid (Node (Member a)) -> Expr a
    toBlock = Block [] . M.map (fmap lift)

    updateMember :: Member a -> Member a -> Member a
    updateMember e w = wrap (unwrap e `Update` unwrap w)
    
    unwrap = unscope . getMember
    wrap = Member . Scope
  updateNode (Open ma)    (Open mb)   = Open (M.unionWith updateNode ma mb)
  
  
memberNode :: Node (Member a) -> Member a
memberNode (Closed a) = a
memberNode (Open m) = (Member . lift) (Block [] (M.map (fmap lift) m))
        
    
instantiateSelf :: M.Map Tid (Node (Member a)) -> M.Map Tid (Expr a)
instantiateSelf se = m
  where
    m = M.map
      (exprNode . fmap
        (instantiate (\ k ->
          (maybe (Undef (Pub k)) id) (M.lookup k m))
        . getMember))
      se
      
    exprNode :: Node (Expr a) -> Expr a
    exprNode (Closed e) = e
    exprNode (Open m) = Block [] ((M.map . fmap) (lift . Member . lift) m)
    

fixField :: Tid -> M.Map Tid (Node (Member a)) -> Either (EvalError Id) (M.Map Tid (Node (Member a)))
fixField x se = maybe
  (Left (LookupFailed x))
  (return . go . memberNode)
  (M.lookup x se)
  where 
    go xmbr = (M.map . fmap) (substField x xmbr) (M.delete x se)
    
    
    substField :: Tid -> Member a -> Member a -> Member a
    substField x m1 m2 = (Member . Scope)
      (unscope (getMember m2) >>= \ v -> case v of
        B b -> if b == x then unscope (getMember m1) else return v
        F a -> return v)
      