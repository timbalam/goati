{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE EmptyCase, TypeOperators, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, DataKinds, PolyKinds, ScopedTypeVariables, ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances, FunctionalDependencies #-}
module Goat.Comp
  ( Comp(..)
  , sends, iter, hoist, run
  , Union
  , injU, weakenU, handleU, handleAllU, sendU
  , (<:)(..), Null
  , Member(..), MemberU(..), MemberU2(..) --, MemberURec(..)
  , send, handle, resends
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

iter
  :: (forall x . eff x -> (x -> r) -> r)
  -> (a -> r)
  -> Comp eff a -> r
iter kf ka (Done a) = ka a
iter kf ka (Req r k) = kf r (iter kf ka . k)

hoist :: (forall x . eff x -> eff' x) -> Comp eff a -> Comp eff' a
hoist f (Done a) = Done a
hoist f (Req r k) = Req (f r) (hoist f . k)

-- |
newtype Union r a = Union (r a)
  
-- | Open union
data (f <: g) a = Head (f a) | Tail (g a)
--data (f *: g) a = Compose { getCompose :: f (g a) }
data Null a


send :: Member h eff => h a -> Comp eff a
send h = sends (inj h) Done

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
    
handleAll
 :: (Comp r a -> Comp Null a) -> Comp r Void -> a
handleAll f = run . f . vacuous

run :: Comp Null a -> a
run (Done a) = a

injU :: Member h eff => h a -> Union eff a
injU h = Union (inj h)

sendU :: Union r a -> Comp r a
sendU (Union r) = sends r Done

weakenU :: Union t a -> Union (h <: t) a
weakenU (Union r) = Union (Tail r)
{-
decompU :: Union (h <: t) a -> Either (h a) (Union t a)
decompU (Union (Head h)) = Left h
decompU (Union (Tail t)) = Right (Union t)

voidU :: Union Null a -> b
voidU (Union a) = case a of {}
-}
handleAllU
 :: (forall y . (forall x . (x -> b) -> Union Null x -> b) ->
      (y -> b) ->
      Union r y -> b)
 -> (a -> b) -> Union r a -> b
handleAllU f = f ( \ _ (Union a) -> case a of {})

handleU
 :: (forall x . (x -> r) -> h x -> r)
 -> (forall x . (x -> r) -> Union t x -> r)
 -> (a -> r) -> Union (h <: t) a -> r
handleU kh kt ka (Union (Head h)) = kh ka h
handleU kh kt ka (Union (Tail t)) = kt ka (Union t)

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
  minj _ h = Head h
  mprj _ (Head h) = Just h
  mprj _ _ = Nothing

instance
  Member' h t n => Member' h (h' <: t) (S n)
  where
    minj _ h = Tail (minj (P :: P n) h)
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
  Member (tag (UIndex tag r)) r => MemberU (tag :: k -> * -> *) r
  where
    type UIndex tag r :: k
instance
  MemberU' (IsTag tag r) tag r => MemberU tag r
  where
    type UIndex tag r = UIndex' (IsTag tag r) tag r

class
  MemberU (tag (U2Index tag r)) r
   => MemberU2 (tag :: k1 -> k2 -> * -> *) r
  where
    type U2Index tag r :: k1
instance
  MemberU2' (IsTag2 tag r) tag r => MemberU2 tag r
  where
    type U2Index tag r = U2Index' (IsTag2 tag r) tag r
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

instance MemberU' True tag (tag e <: t) where
  type UIndex' True tag (tag e <: t) = e

instance
  (Member (tag (UIndex tag t)) (h <: t), MemberU tag t)
   => MemberU' False tag (h <: t)
  where
    type UIndex' False tag (h <: t) = UIndex tag t

class
  MemberU (tag (U2Index' f tag r)) r
   => MemberU2' (f :: Bool) (tag :: k1 -> k2 -> * -> *) r
  where
    type U2Index' f tag r :: k1

instance MemberU2' True tag (tag a b <: t) where
  type U2Index' True tag (tag a b <: t) = a

instance
  ( MemberU (tag (U2Index tag t)) (h <: t)
  , MemberU2 tag t
  )
   => MemberU2' False tag (h <: t)
  where
    type U2Index' False tag (h <: t) = U2Index tag t
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

class Membered (m :: * -> *) where type Members m :: k -> *
instance Membered (Comp r) where type Members (Comp r) = r
instance Membered (Union r) where type Members (Union r) = r
{--}
class
  MemberU tag r =>
    MemberUM
      tag
      (t :: (* -> *) -> * -> *)
      (r :: * -> *)
  where
    type UIndexM tag t r :: * -> *

instance
 MemberU tag r
  => MemberUM (tag :: ((* -> *) -> * -> *) -> * -> *) t r where
  type UIndexM tag t r = UIndex tag r (t r)

instance MemberUM Extend (Comp r) => Extend_ (Comp r) where
  type Ext (Comp r) = UIndexM Extend (Comp r)
-}

