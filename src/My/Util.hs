{-# LANGUAGE FlexibleContexts, DeriveFunctor, GeneralizedNewtypeDeriving #-}

-- | Module of miscellaneous tools

module My.Util
  ( Collect(..), collect
  , unionAWith
  , (<&>)
  , Susp(..)
  )
where
  
import Data.Bifunctor
import Data.Foldable
import Data.Bitraversable
import Data.Semigroup
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
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
  
  
-- | 
data ZipA f a = ZipP a | ZipA (f (ZipA a))
  deriving Functor
  
instance Applicative f => Applicative (ZipA f) where
  pure = ZipP
  
  ZipP f <*> ZipP a = ZipP (f a)
  ZipP f <*> ZipA ma = ZipA (fmap f <$> ma)
  ZipA mf <*> ZipP a = ZipA (fmap ($ a) <$> mf)
  ZipA mf <*> ZipA ma = ZipA (liftA2 (<*>) mf ma)
  
  
