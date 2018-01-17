module Eval
  ( getField
  , eval
  )
where

import Types.Expr
import Types.Error
import Primop( numberSelf, boolSelf )

import Data.List.NonEmpty( NonEmpty )
import Data.Bifunctor
import Data.Maybe( fromMaybe )
import Control.Applicative( liftA2 )
import Control.Monad( join, (<=<) )
import Control.Monad.Trans
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Bound


eval :: Expr a -> IO (Expr a)
eval (e `At` x)    = getField e x
eval (Primop op)   = evalPrimop op
eval e             = return e


getField :: Expr a -> Tid -> IO (Expr a)
getField e x = do
  m <- self e
  e <- maybe
    (error ("getField: " ++ show x))
    return
    (M.lookup x (instantiateSelf m))
  eval e


self :: Expr a -> IO (M.Map Tid (Node (Member a)))
self (Number d)     = return (numberSelf d)
self (String s)     = error "self: String"
self (Bool b)       = return (boolSelf b)
self (Block en se)  = return (M.map
  (instantiate (memberNode . (en' !!)) . unE <$>)
  se) where
  en' = map (instantiate (memberNode . (en' !!)) . unE <$>) en
self (e `At` x)     = getField e x >>= self
self (e `Fix` m)    = flip fixNode m <$> self e where
self (e `Update` w) = liftA2 (M.unionWith updateNode) (self e)
  (self w) where    
  updateNode :: Node (Member a) -> Node (Member a) -> Node (Member a)
  updateNode _            (Closed a)  = Closed a
  updateNode (Closed a)   (Open m)    = (Closed . updateMember a
    . lift) (toBlock m) where
    toBlock :: M.Map Tid (Node (Member a)) -> Expr a
    toBlock = Block [] . M.map (E . lift <$>)

    updateMember :: Member a -> Member a -> Member a
    updateMember e w = wrap (Update (unwrap e) (unwrap w))
    
    unwrap = unscope
    wrap = Scope
  updateNode (Open ma)    (Open mb)   = Open (M.unionWith updateNode ma mb)
  
  
memberNode :: Node (Member a) -> Member a
memberNode (Closed a) = a
memberNode (Open m) = lift (Block [] (M.map (E . lift <$>) m))
        
    
instantiateSelf :: M.Map Tid (Node (Member a)) -> M.Map Tid (Expr a)
instantiateSelf se = m
  where
    m = M.map
      (exprNode . fmap
        (instantiate (\ k -> fromMaybe
          (error ("instantiateSelf: " ++ show k))
          (M.lookup k m))))
      se
      
    exprNode :: Node (Expr a) -> Expr a
    exprNode (Closed e) = e
    exprNode (Open m) = Block [] (M.map (lift <$>) m)
    
    
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
      
  unwrap = unscope
  wrap = Scope
    

evalPrimop :: Primop (Expr a) -> IO (Expr a)
evalPrimop (NumberBinop op a e) = (\ e -> let
  n = case e of
    Number d -> d
    _ -> error "builtin: Number"
  in case op of
    AddNumber -> Number (a + n)
    SubNumber -> Number (a - n)
    ProdNumber -> Number (a * n)
    DivNumber -> Number (a / n)
    PowNumber -> Number (a ** n)
    EqNumber -> Bool (a == n)
    NeNumber -> Bool (a /= n)
    LtNumber -> Bool (a < n)
    GtNumber -> Bool (a > n)
    GeNumber -> Bool (a >= n)
    LeNumber -> Bool (a <= n)) <$> eval e
    
evalPrimop (BoolBinop op a e) = (\ e -> let
  b = case e of
    Bool b -> b
    _ -> error "builtin: Bool"
  in case op of
    AndBool -> Bool (a && b)
    OrBool -> Bool (a || b)
    EqBool -> Bool (a == b)
    NeBool -> Bool (a /= b)
    LtBool -> Bool (a < b)
    GtBool -> Bool (a > b)
    LeBool -> Bool (a <= b)
    GeBool -> Bool (a >= b)) <$> eval e
    
   
   