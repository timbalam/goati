{-# LANGUAGE ExistentialQuantification, TypeOperators, RankNTypes, MultiParamTypeClasses, PolyKinds, KindSignatures, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Comp
  ( Comp(..), send, iter, hoist --, simple
  , Member(..), MemberU(..), MemberU2(..)
  , MonadFree(..)
  )
  where

import Goat.Prism
import Control.Monad (ap, liftM, join)
import Control.Monad.Free (MonadFree(..))
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

instance MonadFree f (Comp f) where
  wrap f = join (send f)

comp
 :: (a -> r)
 -> (forall x . eff x -> (x -> r) -> r)
 -> Comp eff a -> r
comp ka kf (Done a) = ka a
comp ka kf (Req r k) = kf r (comp ka kf . k)

iter :: Functor eff => (eff a -> a) -> Comp eff a -> a
iter f = comp id (\ r k -> f (k <$> r))

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

class Member (tag (UIndex tag r)) r => MemberU tag r where
  type UIndex tag r :: k

class
  Member (tag (U2Index tag r) (U1Index tag r)) r
   => MemberU2 (tag :: k1 -> k2 -> * -> *) r
 where
    type U2Index tag r :: k2
    type U1Index tag r :: k1

{-
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
-}