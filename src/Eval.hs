{-# LANGUAGE OverloadedStrings #-}
module Eval
  ( getField
  , eval 
  )
where

import Types.Expr
import Types.Error

import qualified Data.Maybe as Maybe
import Data.List.NonEmpty( NonEmpty )
import Data.Bifunctor
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


eval :: Expr a -> Either (EvalError Id) (Expr a)
eval (e `At` x) = getField e x
eval (Builtin op e) = evalBuiltin op <$> eval e
eval e          = return e


getField :: Expr a -> Tid -> Either (EvalError Id) (Expr a)
getField e x = do
  m <- self e
  e <- maybe
    (Left (LookupFailed x))
    return
    (M.lookup x (instantiateSelf m))
  eval e


self :: Expr a -> Either (EvalError Id) (M.Map Tid (Node (Member a)))
self (Number d)     = return (selfNumber d)
self (String s)     = error "Self: String"
self (Bool b)       = return (selfBool b)
self (Block en se)  = return ((M.map . fmap)
  (instantiate (memberNode . (en' !!)))
  se) where
  en' = (map . fmap) (instantiate (memberNode . (en' !!))) en
self (e `At` x)     = getField e x >>= self
self (e `Fix` m)    = flip fixNode m <$> self e where
self (e `Update` w) = liftA2 (M.unionWith updateNode) (self e)
  (self w) where    
  updateNode :: Node (Member a) -> Node (Member a) -> Node (Member a)
  updateNode _            (Closed a)  = Closed a
  updateNode (Closed a)   (Open m)    = (Closed . updateMember a
    . Member . lift) (toBlock m) where
    toBlock :: M.Map Tid (Node (Member a)) -> Expr a
    toBlock = Block [] . M.map (fmap lift)

    updateMember :: Member a -> Member a -> Member a
    updateMember e w = wrap (Update (unwrap e) (unwrap w))
    
    unwrap = unscope . getMember
    wrap = Member . Scope
  updateNode (Open ma)    (Open mb)   = Open (M.unionWith updateNode ma mb)
  
  
memberNode :: Node (Member a) -> Member a
memberNode (Closed a) = a
memberNode (Open m) = (Member . lift) 
  (Block [] (M.map (fmap lift) m))
        
    
instantiateSelf :: M.Map Tid (Node (Member a)) -> M.Map Tid (Expr a)
instantiateSelf se = m
  where
    m = M.map
      (exprNode . fmap
        (instantiate (\ k -> Maybe.fromJust (M.lookup k m))
        . getMember))
      se
      
    exprNode :: Node (Expr a) -> Expr a
    exprNode (Closed e) = e
    exprNode (Open m) = Block [] ((M.map . fmap) (lift . Member . lift) m)
    
    
fixNode :: M.Map Tid (Node (Member a)) -> M.Map Tid (Node ()) -> M.Map Tid (Node (Member a))
fixNode se m = (M.map . fmap) (substNode closedmbrs) se' where
  closedmbrs = memberNode <$> M.intersection se (M.filter isClosed m)
  se' = M.differenceWith fixOpen se m
  
  isClosed :: Node a -> Bool 
  isClosed (Closed _) = True
  isClosed (Open _) = False
    
  fixOpen :: Node (Member a) -> Node () -> Maybe (Node (Member a))
  fixOpen _ (Closed ()) = Nothing
  fixOpen (Closed mbr) (Open m) = (Just . Closed . wrap)
    (unwrap mbr `Fix` m)
  fixOpen (Open ma) (Open mb) = (Just . Open)
    (M.differenceWith fixOpen ma mb)
     
  substNode :: M.Map Tid (Member a) -> Member a -> Member a
  substNode m mbr = wrap
    (unwrap mbr >>= \ v -> case v of
      B b -> maybe (return v) unwrap (M.lookup b m)
      F a -> return v)
      
  unwrap = unscope . getMember
  wrap = Member . Scope
      
      
selfNumber :: Double -> M.Map Tid (Node (Member a))
selfNumber d = M.fromList [
  (Label "neg", (Closed . Member . lift . Number) (-d)),
  (Label "add", nodeBuiltin (AddNumber d)),
  (Label "sub", nodeBuiltin (SubNumber d)),
  (Label "prod", nodeBuiltin (ProdNumber d)),
  (Label "div", nodeBuiltin (DivNumber d)),
  (Label "pow", nodeBuiltin (PowNumber d)),
  (Label "gt", nodeBuiltin (GtNumber d)),
  (Label "lt", nodeBuiltin (LtNumber d)),
  (Label "eq", nodeBuiltin (EqNumber d)),
  (Label "ne", nodeBuiltin (NeNumber d)),
  (Label "ge", nodeBuiltin (GeNumber d)),
  (Label "le", nodeBuiltin (LeNumber d))
  ]
  
  
selfBool :: Bool -> M.Map Tid (Node (Member a))
selfBool b = M.fromList [
  (Label "not", (Closed . Member . lift . Bool) (not b)),
  (Label "and", nodeBuiltin (AndBool b)),
  (Label "or", nodeBuiltin (OrBool b))
  ]
  
  
nodeBuiltin :: Builtin -> Node (Member a)
nodeBuiltin op = (Closed . Member . lift . Block [] . M.fromList) [
  (Label "y", (Closed . lift . Member . Scope . Builtin op . Var . B) (Label "x"))
  ]
    

evalBuiltin :: Builtin -> Expr a -> Expr a
evalBuiltin op e = case op of
  AddNumber a -> Number (a + n)
  SubNumber a -> Number (a - n)
  ProdNumber a -> Number (a * n)
  DivNumber a -> Number (a / n)
  PowNumber a -> Number (a ** n)
  GtNumber a -> Bool (a > n)
  LtNumber a -> Bool (a < n)
  EqNumber a -> Bool (a == n)
  NeNumber a -> Bool (a /= n)
  GeNumber a -> Bool (a >= n)
  LeNumber a -> Bool (a <= n)
  AndBool a -> Bool (a && b)
  OrBool a -> Bool (a || b)
  where
    n = case e of Number d -> d; _ -> error "builtin: Number"
    b = case e of Bool b -> b; _ -> error "builtin: Bool"
    
   
   