{-# LANGUAGE FlexibleContexts, OverloadedStrings, DeriveFunctor #-}
module Types.Core
  ( Expr(..)
  , Vis(..)
  , Tag
  , ShowMy(..)
  , M
  , pathM
  , blockM
  , S
  , pathS
  , punS
  , blockS
  )
  where
  

import Types.Parser( ShowMy(..), Tag, Field(..), Path, Vis(..) )
import qualified Types.Error as E

import Control.Applicative (liftA2)
import Control.Monad.Free
import qualified Data.Map as M
import Bound


-- Interpreted my-language expression
data Expr a =
    String T.Text
  | Number Double
  | Bool Bool
  | Var a
  | Block (M.Map Tag (Scope Tag Expr a))
  | Expr a `Concat` Expr a
  | Expr a `At` Tag
  | Expr a `Del` Tag
  | Expr a `Update` Expr a
  deriving (Eq, Functor, Foldable, Traversable)
  
  
instance Monad Expr where
  return = Var
  
  
  String s >>= f =
    String s
    
  Number d >>= f =
    Number d
    
  Bool b >>= f =
    Bool b
    
  Var a >>= f =
    f a
    
  Block m e >>= f =
    Block (map (>>>= f) xs) (e >>= f)
    
  e `At` x >>= f =
    (e >>= f) `At` x
    
  e `Del` x >>= f =
    (e >>= f) `Del` x
    
  e1 `Update` e2 >>= f
    (e1 >>= f) `Update` (e2 >>= f)
  
  
instance ShowMy a => ShowMy (Expr a) where
  showMy (String x) =
    show x
  
  showMy (Number x) =
    show x
    
  showMy (Bool x)   =
    show x
    
  showMy (Var a) =
    showMy a
    
  showMy (Block m) =
    "<Node>"
    
  showMy (Concat a b) =
    showsMy a ("|" ++ showMy b)
    
  showMy (e `At` x) =
    showsMy e ("." ++ showMy x)
    
  showMy (e `Del` x) =
    showsMy e ("~" ++ showMy x)
    
  showMy (e1 `Update` e2) =
    showsMy e1 ("(" ++ showsMy e2 ")")
    
    
    
-- Match expression tree
data M a = V a | Tr (M.Map Tag (M a))

emptyM = Tr M.empty


mergeM :: M a -> M a -> Maybe (M a)
mergeM (Tr m) (Tr n)  = Tr <$> unionAWith mergeM m n
mergeM _      _       = Nothing


instance Monoid (Maybe (M a)) where
  mempty = Just emptyM
  
  
  mappend = join . liftA2 mergeM


-- Set expression tree
data S a = S (M.Map a (M (Expr a)))

emptyS = S M.empty


mergeS :: S a -> S a -> Maybe (S a)    
mergeS (S a) (S b) =
  S <$> unionAWith mergeM a b
  
  
instance Monoid (Maybe (S a)) where
  mempty = Just emptyS
  
  mappend = join . liftA2 mergeS
  


pathS :: Path a -> Expr a -> S a
pathS path = tree path . V


punS :: Path a -> S a
punS path = tree path emptyS


tree :: Path a -> a -> S a
  where
    go (Pure a) =
      S . M.singleton a
      
    go (Free (path `At` x)) =
      go path . Tr . M.singleton x

  
pathM :: Path Tag -> a -> M a
pathM path = go path . V
  where
    go (Pure x) =
      Tr . M.singleton x

    go (Free (path `At` x)) =
      go path . Tr . M.singleton x
      

blockM :: (Expr a -> Maybe (S a)) -> M (Expr a -> Maybe (S a)) -> Expr a -> Maybe (S a)
blockM rest = go1
  where
    go1, go :: M (Expr a -> Maybe (S a)) -> Expr a -> Maybe (S a)
    go1 (V f) e = f e 
    
    go1 (Tr m) e =
      (rest . foldr (flip Del) e) (M.keys m) <> go (Tr m) e
    
    
    go (V f) e = f e
    
    go (Tr m) e =
      M.foldMapWithKey (flip go . Proj e) m
  

blockS :: S (Vis Tag) -> Expr (Vis Tag)
blockS (S m) =
  Block self
  where
    (self, env) =
      partition (map go m)
      
    
    substPriv :: Vis Tag -> Expr (Vis Tag)
    substPriv =
      vis
        (return . Pub)
        (maybe (return . Priv) id . flip M.lookup env)
    
    
    go1 :: M (Expr (Vis Tag)) -> Scope Tag Expr (Vis Tag)
    go1 (V e) = abstract maybePub (e >>= substPriv)
    go1 (Tr m) = Scope (Block m')
      where
        -- Scope :: Expr (Var Tag (Expr (Vis Tag))) -> Scope Tag Expr (Vis Tag)
        -- Block :: M.Map Tag (Scope Tag Expr (Var Tag (Expr (Vis Tag)))) -> Expr (Var Tag (Expr (Vis Tag)))
        -- k :: Scope Tag Expr (Vis Tag) -> Scope Tag Expr (Var Tag (Expr (Vis Tag))
        m' = M.mapWithKey (lift . unscope . go . Var . Pub) m
        
        
    go:: Expr (Vis Tag) -> M (Expr (Vis Tag)) -> Scope Tag Expr (Vis Tag)
    go _ a@(V _) = go1 a
    go e (Tr m) = (Scope . Concat (Block m') . unscope) (abstract maybePub e')
      where
        m' = mapWithKey (lift . unscope . go . At e) m
        e' = foldr (flip Del) e (M.keys m)
    
    
    partition :: M.Map (Vis a) b -> (M.Map a b, M.Map a b)
    partition =
      foldrWithKey
        (\ k a (s, e) ->
          case k of
            Priv x -> (s, M.insert x a e)
            Pub x -> (M.insert x a s, e))
        (M.empty, M.empty)
        
  
  
unionAWith :: (a -> b -> f c) -> M.Map k a -> M.Map k b -> f (M.Map k c)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    M.zipWithAMatched (\ _ -> f)
    
