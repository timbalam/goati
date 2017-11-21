{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Core
  ( Expr(..)
  , Tag
  , ShowMy(..)
  , MRes(..)
  , M
  , pathM
  , blockM
  , S
  , pathS
  , punS
  , blockS
  , Vis(..)
  , vis
  , maybePub
  , maybePriv
  )
  where
  

import Types.Parser( ShowMy(..), Tag, Path )
import qualified Types.Parser as TP
import Parser ( Vis(..), vis, maybePub, maybePriv )
import qualified Types.Error as E

import Control.Applicative ( liftA2 )
import Control.Monad ( join )
import Control.Monad.Free
import Control.Monad.Trans
import Data.Monoid ( (<>) )
import Data.Functor.Classes
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
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
  deriving (Functor, Foldable, Traversable)
  
  
instance Eq1 Expr


instance Applicative Expr
  
  
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
    
  Block m >>= f =
    Block (M.map (>>>= f) m)
    
  e `At` x >>= f =
    (e >>= f) `At` x
    
  e `Del` x >>= f =
    (e >>= f) `Del` x
    
  e1 `Update` e2 >>= f =
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
newtype MRes a = MRes { getresult :: Maybe a }
  deriving (Functor, Applicative, Monad)
  
  
data M a = V a | Tr (M.Map Tag (M a))

emptyM = Tr M.empty


mergeM :: M a -> M a -> MRes (M a)
mergeM (Tr m) (Tr n)  = Tr <$> unionAWith mergeM m n
mergeM _      _       = MRes Nothing


instance Monoid (MRes (M a)) where
  mempty = pure emptyM
  
  a `mappend` b = join (liftA2 mergeM a b)


-- Set expression tree
data S a = S (M.Map a (M (Expr a)))

emptyS = S M.empty


mergeS :: Ord a => S a -> S a -> MRes (S a)    
mergeS (S a) (S b) =
  S <$> unionAWith mergeM a b
  
  
instance Ord a => Monoid (MRes (S a)) where
  mempty = pure emptyS
  
  a `mappend` b = join (liftA2 mergeS a b)
  


pathS :: Path a -> Expr a -> S a
pathS path = tree path . V


punS :: Path a -> S a
punS path = tree path emptyM


tree :: Path a -> M (Expr a) -> S a
tree = go
  where
    go (Pure a) =
      S . M.singleton a
      
    go (Free (path `TP.At` x)) =
      go path . Tr . M.singleton x

  
pathM :: Path Tag -> a -> M a
pathM path = go path . V
  where
    go (Pure x) =
      Tr . M.singleton x

    go (Free (path `TP.At` x)) =
      go path . Tr . M.singleton x
      

blockM :: Monoid m => (Expr a -> m) -> M (Expr a -> m) -> Expr a -> m
blockM rest = go1
  where
    --go1, go :: Monoid m => M (Expr a -> m) -> Expr a -> m
    go1 (V f) e = f e 
    
    go1 (Tr m) e =
      (rest . foldr (flip Del) e) (M.keys m) <> go (Tr m) e
    
    
    go (V f) e = f e
    
    go (Tr m) e =
      M.foldMapWithKey (flip go . At e) m
  

blockS :: S (Vis Tag) -> Expr (Vis Tag)
blockS (S m) =
  Block self
  where
    (self, env) =
      partition (M.map go1 m)
      
    
    substPriv :: Vis Tag -> Scope Tag Expr (Vis Tag)
    substPriv =
      vis
        (return . Pub)
        (\ k -> (maybe . return) (Priv k) id (M.lookup k env))
    
    
    go1 :: M (Expr (Vis Tag)) -> Scope Tag Expr (Vis Tag)
    go1 (V e) = abstract maybePub e >>= substPriv
    go1 (Tr m) = Scope (Block m')
      where
        -- Scope :: Expr (Var Tag (Expr (Vis Tag))) -> Scope Tag Expr (Vis Tag)
        -- Block :: M.Map Tag (Scope Tag Expr (Var Tag (Expr (Vis Tag)))) -> Expr (Var Tag (Expr (Vis Tag)))
        -- k :: Scope Tag Expr (Vis Tag) -> Scope Tag Expr (Var Tag (Expr (Vis Tag))
        m' = M.mapWithKey (\ k -> lift . unscope . (go . Var) (Pub k)) m
        
        
    go :: Expr (Vis Tag) -> M (Expr (Vis Tag)) -> Scope Tag Expr (Vis Tag)
    go _ a@(V _) = go1 a
    go e (Tr m) = (Scope . Concat (Block m') . unscope) (abstract maybePub e')
      where
        m' = M.mapWithKey (\ k -> lift . unscope . go (e `At` k)) m
        e' = foldr (flip Del) e (M.keys m)
    
    
    partition :: Ord a => M.Map (Vis a) b -> (M.Map a b, M.Map a b)
    partition =
      M.foldrWithKey
        (\ k a (s, e) ->
          case k of
            Priv x -> (s, M.insert x a e)
            Pub x -> (M.insert x a s, e))
        (M.empty, M.empty)
        
  
  
unionAWith :: (Applicative f, Ord k) => (a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched (\ _ -> f))
    
