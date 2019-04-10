{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE EmptyCase, TypeOperators, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, DataKinds, PolyKinds, ScopedTypeVariables, ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances, FunctionalDependencies #-}
module Goat.Comp
  ( Comp(..)
  , sends, iter, hoist, run
  , (<:)(..), Null, Member(..), MemberU(..), MemberU2(..)
  , send, weaken, handle, resends
  , handleAll
  )
  where

import Control.Monad (ap, liftM)
import Data.Void (Void, vacuous)

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

send :: eff a -> Comp eff a
send r = sends r pure

iter
  :: (forall x . eff x -> (x -> r) -> r)
  -> (a -> r)
  -> Comp eff a -> r
iter kf ka (Done a) = ka a
iter kf ka (Req r k) = kf r (iter kf ka . k)

hoist :: (forall x . eff x -> eff' x) -> Comp eff a -> Comp eff' a
hoist f (Done a) = Done a
hoist f (Req r k) = Req (f r) (hoist f . k)
  
-- | Open union
newtype Union r a = Union { getUnion :: r a }
data (f <: g) a = Head (f a) | Tail (g a)
--data (f *: g) a = Compose { getCompose :: f (g a) }
data Null a

weaken :: Union t a -> Union (h <: t) a
weaken (Union r) = Union (Tail r)

handle
 :: (forall x . h x -> (x -> Comp (Union t) a) -> Comp (Union t) a)
 -> Comp (Union (h <: t)) a -> Comp (Union t) a
handle f =
  iter
    (\ (Union r) k -> case r of
      Head h -> f h k
      Tail t -> Req (Union t) k)
    Done

resends
 :: (forall x . h x ->
      (x -> Comp (Union (h' <: t)) a) ->
      Comp (Union (h' <: t)) a)
 -> Comp (Union (h <: t)) a -> Comp (Union (h' <: t)) a
resends f =
  iter
    (\ (Union r) k -> case r of
      Head h -> f h k
      Tail t -> Req (Union (Tail t)) k)
    Done
    
handleAll
 :: (Comp (Union r) a -> Comp (Union Null) a)
 -> Comp (Union r) Void -> a
handleAll f = run . f . vacuous

run :: Comp (Union Null) a -> a
run (Done a) = a

-- | Union membership
data Nat = Z | S Nat
type family FindElem (h :: * -> *) r :: Nat where
  FindElem h (Union (h <: t)) = Z
  FindElem h (Union (h' <: t)) = S (FindElem h (Union t))

data P (n :: Nat) = P
class Member' h r (n :: Nat) where
  minj :: P n -> h x -> r x
  mprj :: P n -> r x -> Maybe (h x)

instance Member' h (Union (h <: t)) Z where
  minj _ h = Union (Head h)
  mprj _ (Union (Head h)) = Just h
  mprj _ _ = Nothing

instance
  Member' h (Union t) n => Member' h (Union (h' <: t)) (S n)
  where
    minj _ h = Union (Tail (getUnion (minj (P :: P n) h)))
    mprj _ (Union (Head _)) = Nothing
    mprj _ (Union (Tail t)) = mprj (P :: P n) (Union t)

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
  Member (tag (UIndex tag r)) r => MemberU (tag :: k -> * -> *) r
  where
    type UIndex tag r :: k
instance
  MemberU' (IsTag tag r) tag (Union r) => MemberU tag (Union r)
  where
    type UIndex tag (Union r) = UIndex' (IsTag tag r) tag (Union r)

class
  MemberU (tag (U2Index tag r)) r
   => MemberU2 (tag :: k1 -> k2 -> * -> *) r
  where
    type U2Index tag r :: k1
instance
  MemberU2' (IsTag2 tag r) tag (Union r) => MemberU2 tag (Union r)
  where
    type U2Index tag (Union r) = U2Index' (IsTag2 tag r) tag (Union r)
{-
class
  Member (tag (UIndex1 tag r) (UIndex2 tag r)) r
   => MemberU2 (tag :: k1 -> k2 -> * -> *) r
  where
    type UIndex1 tag r :: k1
    type UIndex2 tag r :: k2
instance
  MemberU2' (IsTag2 tag r) tag r => MemberU2 tag r
  where
    type UIndex1 tag r = UIndex1' (IsTag2 tag r) tag r
    type UIndex2 tag r = UIndex2' (IsTag2 tag r) tag r
-}
class
  Member (tag (UIndex' f tag r)) r
   => MemberU' (f :: Bool) (tag :: k -> * -> *) r
  where
    type UIndex' f tag r :: k

instance MemberU' True tag (Union (tag e <: t)) where
  type UIndex' True tag (Union (tag e <: t)) = e

instance
  ( Member (tag (UIndex tag (Union t))) (Union (h <: t))
  , MemberU tag (Union t)
  )
   => MemberU' False tag (Union (h <: t))
  where
    type UIndex' False tag (Union (h <: t)) = UIndex tag (Union t)

class
  MemberU (tag (U2Index' f tag r)) r
   => MemberU2' (f :: Bool) (tag :: k1 -> k2 -> * -> *) r
  where
    type U2Index' f tag r :: k1

instance MemberU2' True tag (Union (tag a b <: t)) where
  type U2Index' True tag (Union (tag a b <: t)) = a

instance
  ( MemberU (tag (U2Index tag (Union t))) (Union (h <: t))
  , MemberU2 tag (Union t)
  )
   => MemberU2' False tag (Union (h <: t))
  where
    type U2Index' False tag (Union (h <: t)) = U2Index tag (Union t)
{-
class
  Member (tag (UIndex1' f tag r) (UIndex2' f tag r)) r
   => MemberU2' (f :: Bool) (tag :: k1 -> k2 -> * -> *) r
  where
    type UIndex1' f tag r :: k1
    type UIndex2' f tag r :: k2

instance MemberU2' True tag (tag a b <: t) where
  type UIndex1' True tag (tag a b <: t) = a
  type UIndex2' True tag (tag a b <: t) = b

instance
  (Member (tag (UIndex1 tag t) (UIndex2 tag t)) (h <: t), MemberU2 tag t)
   => MemberU2' False tag (h <: t)
  where
    type UIndex1' False tag (h <: t) = UIndex1 tag t
    type UIndex2' False tag (h <: t) = UIndex2 tag t
-}
