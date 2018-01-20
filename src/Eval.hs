{-# LANGUAGE OverloadedStrings #-}
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
import qualified Data.Text.IO as T
import qualified System.IO.Error as IO
import Bound


eval :: Expr a -> Expr a
eval (e `At` x) = getField e x
eval (Prim p)   = evalPrimop p
eval e          = return e


getField :: Expr a -> Tid -> Expr a
getField e x = do
  m <- self e
  e <- maybe
    (error ("getField: " ++ show x))
    return
    (M.lookup x (instantiateSelf m))
  eval e


self :: Expr a -> M.Map Tid (Node (Member a))
self (Number d)     = numberSelf d
self (String s)     = error "self: String"
self (Bool b)       = boolSelf b
self (Block en se)  = M.map
  (instantiate (memberNode . (en' !!)) . unE <$>)
  se where
  en' = map (instantiate (memberNode . (en' !!)) . unE <$>) en
self (e `At` x)     = self (getField e x)
self (e `Fix` m)    = fixNode (self e) m where
self (e `Update` w) = M.unionWith updateNode (self e) (self w)
  where    
    updateNode
      :: Node (Member a) -> Node (Member a) -> Node (Member a)
    updateNode _ (Closed a) =
      Closed a
      
    updateNode (Closed a) (Open m) =
      (Closed . updateMember a . lift) (toBlock m)
      where
        toBlock :: M.Map Tid (Node (Member a)) -> Expr a
        toBlock = Block [] . M.map (E . lift <$>)

        updateMember :: Member a -> Member a -> Member a
        updateMember e w = wrap (Update (unwrap e) (unwrap w))
        
        unwrap = unscope
        wrap = Scope
        
    updateNode (Open ma) (Open mb) =
      Open (M.unionWith updateNode ma mb)
  
  
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
    
    
fixNode
  :: M.Map Tid (Node (Member a))
  -> M.Map Tid (Node ())
  -> M.Map Tid (Node (Member a))
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
    

evalPrimop :: P (Expr a) -> Expr a
evalPrimop p = case p of
  NAdd a e -> nwith (a +) e
  NSub a e -> nwith (a -) e
  NProd a e -> nwith (a *) e
  NDiv a e -> nwith (a /) e
  NPow a e -> nwith (a **) e
  NEq a e -> ncmp (a ==) e
  NNe a e -> ncmp (a /=) e
  NLt a e -> ncmp (a <) e
  NGt a e -> ncmp (a >) e
  NLe a e -> ncmp (a <=) e
  NGe a e -> ncmp (a >=) e
  _       -> Prim p
  where
    nwith f = Number . f . number . eval
    ncmp f = Bool . f . number . eval
    
    number (Number d) = d
    number _          = error "prim: Number"
    
    
    
execPrimop p = case p of
  HGetLine h su er -> hgetwith (T.hGetLine h) su er
    hgetwith f su er = IO.tryIOError f >>= either
      (run er . IOError)
      (run su' . String) where
        su' = su `Update` (Block [] . M.singleton (Label "onError") . Closed) (lift er)
      
  where
    run :: Expr a -> Expr a -> Expr a
    run k v = getField
      (k `Update` (Block [] . M.singleton (Label "val") . Closed) (lift v)) (Label "run")
    
    
   
   