{-# LANGUAGE FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
--{-# LANGUAGE FlexibleInstances #-}

-- | Module of miscellaneous tools

module Goat.Util
  ( --Collect(..), collect
  --, 
    traverseMaybeWithKey
  , restrictKeys
  , withoutKeys
  , (<&>)
  , showsUnaryWith, showsBinaryWith, showsTrinaryWith
  , Compose(..)
  --, WrappedAlign(..)
  , swap, assoc, reassoc
  , abstractEither
  , (...)
  )
where

import Data.Align (Align(..))
import Data.These (These(..), these)
import Data.Bifunctor
import Data.Foldable
import Data.Bitraversable
import Data.Semigroup
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Applicative (liftA2, Alternative(..))
import Control.Monad.Free
import Control.Monad ((<=<), ap)
import Prelude.Extras
import Data.Functor.Classes (readsData)
import Data.Functor.Alt (Alt(..))
import Data.Functor.Plus (Plus(..))
import Bound (Scope(..), Var(..))

infixl 1 <&>

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)


-- | Wrapper for 'Either' with specialised 'Applicative' instance that
--   collects a semigroup 'Left' type. Equivalent to 'Validation'.
newtype Collect a b = Collect { getCollect :: Either a b }
  deriving (Show, Functor, Bifunctor)
  
collect :: a -> Collect a b
collect = Collect . Left

instance Semigroup m => Applicative (Collect m) where
  pure = Collect . Right
  
  Collect (Left m1) <*> Collect (Left m2) = (Collect . Left) (m1 <> m2)
  Collect (Left m)  <*> Collect (Right _) = Collect (Left m)
  Collect (Right _) <*> Collect (Left m)  = Collect (Left m)
  Collect (Right f) <*> Collect (Right a) = (Collect . Right) (f a)
  

traverseMaybeWithKey
  :: Applicative f
  => (k -> a -> f (Maybe b))
  -> M.Map k a
  -> f (M.Map k b)
traverseMaybeWithKey f m = M.mapMaybe id <$> M.traverseWithKey f m

restrictKeys :: Ord k => M.Map k a -> S.Set k -> M.Map k a
restrictKeys m s =
  M.filterWithKey (\ k _ -> k `S.member` s) m
  
withoutKeys :: Ord k => M.Map k a -> S.Set k -> M.Map k a
withoutKeys m s =
  M.filterWithKey (\ k _ -> k `S.notMember` s) m
  
-- | Re-implement helper functions from Data.Functor.Classes (base >= 4.9.0)
readsUnaryWith
  :: (Int -> ReadS a) -> String -> (a -> t) -> String -> ReadS t
readsUnaryWith rp name cons kw s =
  [(cons x, t) | kw == name, (x,t) <- rp 11 s]


showsUnaryWith sp n i a = showParen (i > 10)
  (showString n . showChar ' ' . sp 11 a)
  
showsBinaryWith sp1 sp2 n i a1 a2 = showParen (i > 10)
  (showString n . showChar ' '  . sp1 11 a1 . showChar ' ' . sp2 11 a2)
  
-- | Show a constructor with 3 arguments
showsTrinaryWith sp1 sp2 sp3 n i a1 a2 a3 = showParen (i > 10)
      (showString n . showChar ' ' . sp1 11 a1 . showChar ' ' . sp2 11 a2
        . showChar ' ' . sp3 11 a3)
        
-- | Based on transformers package "Compose" with instances compatible with "Prelude.Extras"
newtype Compose f g a = Compose { getCompose :: f (g a) }
  deriving (Functor, Foldable, Traversable)
  
instance (Applicative f, Applicative g)
  => Applicative (Compose f g) where
  pure x = Compose (pure (pure x))
  Compose f <*> Compose x = Compose ((<*>) <$> f <*> x)
  
instance (Alternative f, Applicative g)
  => Alternative (Compose f g) where
  empty = Compose empty
  Compose x <|> Compose y = Compose (x <|> y)
  
instance (Functor f, Eq1 f, Eq1 g, Eq a)
  => Eq (Compose f g a) where
  Compose x == Compose y = fmap Lift1 x ==# fmap Lift1 y
  
instance (Functor f, Ord1 f, Ord1 g, Ord a)
  => Ord (Compose f g a) where
  compare (Compose x) (Compose y) = compare1 (fmap Lift1 x) (fmap Lift1 y)
  
instance (Functor f, Read1 f, Read1 g, Read a)
  => Read (Compose f  g a) where
  readsPrec = readsData (readsUnaryWith readsPrec1 "Compose" (Compose . fmap lower1))
  
instance (Functor f, Show1 f, Show1 g, Show a)
  => Show (Compose f g a) where
  showsPrec d (Compose x) = showsUnaryWith showsPrec1 "Compose" d (fmap Lift1 x)
  
instance (Functor f, Eq1 f, Eq1 g) => Eq1  (Compose f g) where
  (==#) = (==)
  
instance (Functor f, Ord1 f, Ord1 g) => Ord1 (Compose f g) where
  compare1 = compare
  
instance (Functor f, Read1 f, Read1 g)
  => Read1 (Compose f g) where
  readsPrec1 = readsPrec
  
instance  (Functor f, Show1 f, Show1 g)
  => Show1 (Compose f g) where
  showsPrec1 = showsPrec

instance (Align f, Align g) => Align (Compose f g) where
  nil = Compose nil
  
  alignWith f (Compose fga) (Compose fgb) =
    Compose (alignWith (merge' f) fga fgb) where
      merge' f (This ga) = fmap (f . This) ga
      merge' f (That gb) = fmap (f . That) gb
      merge' f (These ga gb) = alignWith f ga gb 


newtype WrappedAlign f a = WrappedAlign { unwrapAlign :: f a }
  deriving (Functor, Align)

instance
  (Align f, Semigroup a) => Semigroup (WrappedAlign f a)
  where
    WrappedAlign f <> WrappedAlign g =
      WrappedAlign (alignWith (these id id (<>)) f g)

instance
  (Align f, Semigroup a) => Monoid (WrappedAlign f a)
  where
    mempty = WrappedAlign nil
    mappend = (<>)
    
-- | Missing from older version of 'these'
assoc :: These a (These b c) -> These (These a b) c
assoc (This a)              = This (This a)
assoc (That (This b))       = This (That b)
assoc (That (That c))       = That c
assoc (That (These b c))    = These (That b) c
assoc (These a (This b))    = This (These a b)
assoc (These a (That c))    = These (This a) c
assoc (These a (These b c)) = These (These a b) c

reassoc :: These (These a b) c -> These a (These b c)
reassoc (This (This a))       = This a
reassoc (This (That b))       = That (This b)
reassoc (This (These a b))    = These a (This b)
reassoc (That c)              = That (That c)
reassoc (These (This a) c)    = These a (That c)
reassoc (These (That b) c)    = That (These b c)
reassoc (These (These a b) c) = These a (These b c)

swap :: These a b -> These b a
swap (This a)    = That a
swap (That b)    = This b
swap (These a b) = These b a

-- | Missing from earlier version of 'bound' 
abstractEither
 :: Monad m => (a -> Either b c) -> m a -> Scope b m c
abstractEither f m = Scope (m >>= \ a -> case f a of 
  Left b -> return (B b)
  Right c -> return (F (return c)))
  

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
f ... g = \ a b -> f (g a b) -- (.) . (.)
