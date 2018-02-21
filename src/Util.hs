{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Util
  ( Collect(..), collect
  , unionAWith
  , (<&>)
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
  
  
  
-- | Merge maps with an applicative side effect
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
  
