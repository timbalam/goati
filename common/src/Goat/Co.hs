{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE EmptyCase, TypeOperators #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, PolyKinds #-}
module Goat.Co
  ( module Goat.Co
  , module Control.Monad.Free
  )
  where

import Control.Monad (ap, liftM)
import Control.Monad.Free
import Data.Void (absurd)

infixr 1 <:

-- | Resumable computation
data Comp eff a =
    Done a
  | forall x . Req (eff x) (x -> Comp eff a)

instance Functor (Comp f) where
  fmap = liftM
  
instance Applicative (Comp f) where
  pure = Done
  (<*>) = ap

instance Monad (Comp f) where
  return = pure
  Done a >>= f = f a
  Req r k >>= f = Req r (\ a -> k a >>= f)
  
-- | Open union
data (f <: g) a = Head (f a) | Tail (g a)
data Null a

inj :: Comp g a -> Comp (f <: g) a
inj (Done a) = Done a
inj (Req r k) = Req (Tail r) (\ x -> inj (k x))

send :: f (Comp (f <: g) a) -> Comp (f <: g) a
send r = Req (Head r) id

handle
 :: (forall x . f x -> (x -> Comp g a) -> Comp g a)
 -> Comp (f <: g) a -> Comp g a
handle f (Done a) = Done a
handle f (Req (Head r) k) = f r (handle f . k)
handle f (Req (Tail r) k) = Req r (handle f . k)
    
runComp :: Comp Null a -> a
runComp (Done a) = a