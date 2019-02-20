{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE EmptyCase, TypeOperators, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, DataKinds, PolyKinds, ScopedTypeVariables, ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances, FunctionalDependencies #-}
module Goat.Comp
  ( Comp(..)
  , sends, iter, hoist, run
  , (<:)(..), Member(..), MemberU(..), MemberU2(..)
  , send, weaken, handle, resends
  )
  where

import Control.Monad (ap, liftM)

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

send :: Member h r => h a -> Comp r a
send h = sends (inj h) pure

weaken :: Comp t a -> Comp (h <: t) a
weaken = hoist Tail

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

-- | Union membership
data Nat = Z | S Nat
type family FindElem (h :: * -> *) r :: Nat where
  FindElem h (h <: t) = Z
  FindElem h (h' <: t) = S (FindElem h t)

data P (n :: Nat) = P
class Member' h r (n :: Nat) where
  minj :: P n -> h x -> r x
  mprj :: P n -> r x -> Maybe (h x)

instance Member' h (h <: t) Z where
  minj _ = Head
  mprj _ (Head h) = Just h
  mprj _ _ = Nothing

instance Member' h t n => Member' h (h' <: t) (S n) where
  minj _ = Tail . minj (P :: P n)
  mprj _ (Head _) = Nothing
  mprj _ (Tail t) = mprj (P :: P n) t

class Member' h r (FindElem h r) => Member h r where
  inj :: h x -> r x
  prj :: r x -> Maybe (h x)
  
instance Member' h r (FindElem h r) => Member h r where
  inj = minj (P :: P (FindElem h r))
  prj = mprj (P :: P (FindElem h r))

-- | Associated types
type family IsTag (tag :: k -> * -> *) r :: Bool where
  IsTag tag (tag e <: t) = True
  IsTag tag r            = False

type family IsTag2 (tag :: k1 -> k2 -> * -> *) r :: Bool where
  IsTag2 tag (tag a b <: t) = True
  IsTag2 tag r              = False
 
class
  Member (tag (Dep tag r)) r => MemberU (tag :: k -> * -> *) r
  where
    type Dep tag r :: k
instance
  MemberU' (IsTag tag r) tag r => MemberU tag r
  where
    type Dep tag r = Dep' (IsTag tag r) tag r
    
class
  Member (tag (Dep1 tag r) (Dep2 tag r)) r
   => MemberU2 (tag :: k1 -> k2 -> * -> *) r
  where
    type Dep1 tag r :: k1
    type Dep2 tag r :: k2
instance
  MemberU2' (IsTag2 tag r) tag r => MemberU2 tag r
  where
    type Dep1 tag r = Dep1' (IsTag2 tag r) tag r
    type Dep2 tag r = Dep2' (IsTag2 tag r) tag r

class
  Member (tag (Dep' f tag r)) r
   => MemberU' (f :: Bool) (tag :: k -> * -> *) r
  where
    type Dep' f tag r :: k

instance MemberU' True tag (tag e <: t) where
  type Dep' True tag (tag e <: t) = e

instance
  (Member (tag (Dep tag t)) (h <: t), MemberU tag t)
   => MemberU' False tag (h <: t)
  where
    type Dep' False tag (h <: t) = Dep tag t
  
class
  Member (tag (Dep1' f tag r) (Dep2' f tag r)) r
   => MemberU2' (f :: Bool) (tag :: k1 -> k2 -> * -> *) r
  where
    type Dep1' f tag r :: k1
    type Dep2' f tag r :: k2

instance MemberU2' True tag (tag a b <: t) where
  type Dep1' True tag (tag a b <: t) = a
  type Dep2' True tag (tag a b <: t) = b

instance
  (Member (tag (Dep1 tag t) (Dep2 tag t)) (h <: t), MemberU2 tag t)
   => MemberU2' False tag (h <: t)
  where
    type Dep1' False tag (h <: t) = Dep1 tag t
    type Dep2' False tag (h <: t) = Dep2 tag t
