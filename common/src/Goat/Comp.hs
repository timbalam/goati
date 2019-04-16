{-# LANGUAGE ExistentialQuantification, TypeOperators, RankNTypes, MultiParamTypeClasses, TypeFamilies, PolyKinds, KindSignatures #-}
module Goat.Comp
  ( Comp(..), send, iter, hoist, simple
  , Member(..), MemberU(..), MemberU2(..)
  )
  where

import Goat.Prism
import Control.Monad (ap, liftM)
import Data.Functor.Identity (Identity(..))
import Data.Void (Void, vacuous)


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

iter
 :: (forall x . eff x -> (x -> r) -> r)
 -> (a -> r)
 -> Comp eff a -> r
iter kf ka (Done a) = ka a
iter kf ka (Req r k) = kf r (iter kf ka . k)

simple
 :: (forall y .
      (forall x . eff x -> (x -> Identity b) -> Identity c) ->
      eff' y -> (y -> Identity b') -> Identity c')
 -> (forall x . eff x -> (x -> b) -> c)
 -> eff' a -> (a -> b') -> c'
simple hdl f r k =
  runIdentity
    (hdl
      (\ r' k' -> pure (f r' (runIdentity . k')))
      r
      (pure . k))

hoist :: (forall x . eff x -> eff' x) -> Comp eff a -> Comp eff' a
hoist f (Done a) = Done a
hoist f (Req r k) = Req (f r) (hoist f . k)

send :: Member h eff => h a -> Comp eff a
send h = Req (inj h) Done

class Member h r where
  uprism :: Prism' (r a) (h a)
  uprism = prism' inj prj
  
  inj :: h a -> r a
  inj = review uprism
  
  prj :: r a -> Maybe (h a)
  prj = preview uprism

class
  Member (tag (UIndex tag r)) r
   => MemberU (tag :: k -> * -> *) r
  where
    type UIndex tag r :: k

class
  MemberU (tag (U2Index tag r)) r
   => MemberU2 (tag :: k1 -> k2 -> * -> *) r
  where
    type U2Index tag r :: k1