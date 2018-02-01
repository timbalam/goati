{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Util
  ( Collect(..), collect
  )
where
  
import Data.Bifunctor
import Data.Semigroup
import qualified Data.Map as M
import Control.Monad( <=< )


-- Wrapper for Either with specialised Applicative instance and 
-- Monoid instances
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
  
