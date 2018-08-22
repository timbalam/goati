{-# LANGUAGE FlexibleContexts, DeriveFunctor, GeneralizedNewtypeDeriving #-}

-- | Module of miscellaneous tools

module My.Util
  ( Collect(..), collect
  , unionAWith
  , (<&>)
  , Susp(..)
  , Batch(..)
  , showsTrinaryWith
  )
where
  
import Data.Bifunctor
import Data.Foldable
import Data.Bitraversable
import Data.Semigroup
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Control.Applicative (liftA2)
import Control.Monad.Free
import Control.Monad ((<=<), ap)

infixl 1 <&>

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)


-- | Wrapper for 'Either' with specialised 'Applicative' instance that
--   collects a semigroup 'Left' type. Equivalent to 'Validation'.
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


-- | A suspension 'Susp r a b' that can yield with a message 'r'
--   and be resumed with a value 'a' and finally producing a 'b'
data Susp r a b = Susp { yield :: r, resume :: a -> b }
  deriving Functor
  
instance Monoid r => Applicative (Susp r a) where
  pure a = Susp mempty (const a)
  
  Susp r1 f1 <*> Susp r2 f2 = Susp (r1 `mappend` r2) (f1 <*> f2)
  
  
-- | An Free-like structure that applicatively combines layers
data Batch f a = Run a | Batch (f (Batch f a))
  deriving Functor
  
instance Applicative f => Applicative (Batch f) where
  pure = Run
  
  Run f <*> Run a = Run (f a)
  Run f <*> Batch ma = Batch (fmap f <$> ma)
  Batch mf <*> Run a = Batch (fmap ($ a) <$> mf)
  Batch mf <*> Batch ma = Batch (liftA2 (<*>) mf ma)
  
  
-- | Show a constructor with 3 arguments
showsTrinaryWith sp1 sp2 sp3 n i a1 a2 a3 = showParen (i > 10)
      (showString n . sp1 11 a1 . showChar ' ' . sp2 11 a2
        . showChar ' ' . sp3 11 a3)
  
  
