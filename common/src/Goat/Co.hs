{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE EmptyCase, TypeOperators, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Co
  where

import Control.Monad (ap, liftM)
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

sends :: eff x -> (x -> Comp eff a) -> Comp eff a
sends r k = Req r k

iter
  :: (forall x . eff x -> (x -> r) -> r)
  -> (a -> r)
  -> Comp eff a -> r
iter kf ka (Done a) = ka a
iter kf ka (Req r k) = kf r (iter kf ka . k)

hoist :: (forall x . eff x -> eff' x) -> Comp eff a -> Comp eff' a
hoist f (Done a) = Done a
hoist f (Req r k) = Req (f r) (hoist f . k)

run :: Comp Null a -> a
run (Done a) = a
  
-- | Open union
data (f <: g) a = Head (f a) | Tail (g a)
--data (f *: g) a = Compose { getCompose :: f (g a) }
data Null a

inj :: Comp t a -> Comp (h <: t) a
inj = hoist Tail

send :: h (Comp (h <: t) a) -> Comp (h <: t) a
send h = sends (Head h) id

handle
 :: (forall x . h x -> (x -> Comp t a) -> Comp t a)
 -> Comp (h <: t) a -> Comp t a
handle f = 
  iter
    (\ r k -> case r of
      Head h -> f h k
      Tail t -> Req t k)
    Done

resends
 :: (forall x . h x -> (x -> Comp (h' <: t) a) -> Comp (h' <: t) a)
 -> Comp (h <: t) a -> Comp (h' <: t) a
resends f =
  iter
    (\ r k -> case r of
      Head h -> f h k
      Tail t -> Req (Tail t) k)
    Done
    
{-
hoistsend
 :: (forall x . h x -> h' x)
 -> Comp (h <: t) a -> Comp (h' <: t) a
hoistsend f = hoist (\ r -> case r of
  Head h -> Head (f h)
  Tail t -> Tail t)

hoistinj
 :: (forall x . t x -> t' x)
 -> Comp (h <: t) a -> Comp (h <: t') a
hoistinj f = hoist (\ r -> case r of
  Head h -> Head h
  Tail t -> Tail (f t))
-} 

injs
 :: (Comp t (Comp (h <: t) a) -> Comp t (Comp (h <: t) a))
 -> Comp (h <: t) a -> Comp (h <: t) a
injs f a = join (inj (f (return a)))

injs2
 :: (Comp t (Comp (h <: t) a)
     -> Comp t (Comp (h <: t) a)
     -> Comp t (Comp (h <: t) a))
 -> Comp (h <: t) a -> Comp (h <: t) a -> Comp (h <: t) a
injs2 f a b = join (inj (f (return a) (return b)))
