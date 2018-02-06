{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Util
  ( Collect(..), collect
  , unionAWith, traverse2, bitraverse2
  , (<&>), bitraverseFree, bitraverseFree2
  )
where
  
import Data.Bifunctor
import Data.Foldable
import Data.Bitraversable
import Data.Semigroup
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Control.Monad.Free

infixl 1 <&>

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)


-- | Wrapper for Either with specialised Applicative instance and 
-- | Monoid instances
newtype Collect a b = Collect { getCollect :: Either a b }
  deriving (Functor, Bifunctor)
  
  
collect :: a -> Collect a b
collect = Collect . Left


instance Semigroup m => Applicative (Collect m) where
  pure = Collect . Right
  
  Collect (Left m1) <*> Collect (Left m2) = (Collect . Left) (m1 <> m2)
  Collect (Left m)  <*> Collect (Right _) = Collect (Left m)
  Collect (Right _) <*> Collect (Left m)  = Collect (Left m)
  Collect (Right f) <*> Collect (Right a) = (Collect . Right) (f a)
  
  
joinCollect :: Collect a (Collect a b) -> Collect a b
joinCollect = either collect id . getCollect
  
  
-- | Merge maps with an applicative side effect
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
    
-- | Traverse two layers   
traverse2
  :: (Applicative f, Applicative g, Traversable t)
  => (a -> f (g b)) -> t a -> f (g (t b))
traverse2 f = (sequenceA <$>) . traverse f


bitraverse2
  :: (Applicative f, Applicative g, Bitraversable t)
  => (a -> f (g b)) -> (c -> f (g d)) -> t a c -> f (g (t b d))
bitraverse2 f g = (bisequenceA <$>) . bitraverse f g



bitraverseFree
  :: (Bitraversable t, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Free (t a) b
  -> f (Free (t a') b')
bitraverseFree f g = go where
  go (Pure a) = Pure <$> g a 
  go (Free t) = Free <$> bitraverse f go t
  
  
bitraverseFree2
  :: (Bitraversable t, Applicative f, Applicative g)
  => (a -> f (g a'))
  -> (b -> f (g b'))
  -> Free (t a) b
  -> f (g (Free (t a') b'))
bitraverseFree2 f g = (bitraverseFree id id <$>) . bitraverseFree f g


foldTraverse
  :: (Applicative f, Traversable t, Monoid m)
  => (a -> f m) -> t a -> f m 
foldTraverse f = (fold <$>) . traverse f
  
