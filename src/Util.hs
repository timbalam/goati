{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Util
  ( Collect(..), collect
  )
where
  
import Data.Bifunctor
import Data.Semigroup
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M


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


-- | An enhanced monoidal action
class Monoid a => Check a where
  check :: a -> a -> Collect a a
  
  
instance Check a => Monoid (Collect a a) where
  mempty = pure mempty
  
  a `mappend` b = (first unwrapMonoid . joinCollect
    . liftA2 check (first WrappedMonoid a)) (first WrappedMonoid b)
    
    
instance (Check a, Check b) => Monoid (Collect (a, b) (a, b)) where
  mempty = pure (mempty, mempty)
  
  a `mappend` b = liftA2 (,)
    (first (flip (,) mempty) (on mappend (fst <$>) a b))
    (first ((,) mempty)) (on mappend (snd <$> a b))
  
  
  
-- | Merge maps with an applicative side effect
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
    
    
traverse2
  :: (Applicative f, Applicative g, Traversable t)
  => (a -> f (g b)) -> t a -> f (g (t b))
traverse2 f = (sequenceA <$>) . traverse f


bitraverse2
  :: (Applicative f, Applicative g, Bitraversable t)
  => (a -> f (g b)) -> (c -> f (g d)) -> t a c -> f (g (t b d))
bitraverse2 f g = (bisequenceA <$>) . bitraverse f g
  
