{-# LANGUAGE RankNTypes, TypeOperators, DataKinds, KindSignatures, PolyKinds, EmptyCase, TypeFamilies, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Union
  ( (<:)(), Null
  , weaken, decomp, absurdU, handleU, handleUAll
  , Member(..), MemberU(..), MemberU2(..)
  )
  where

infixr 1 <:

-- | Open union
data (f <: g) a = Head (f a) | Tail (g a)
--data (f *: g) a = Compose { getCompose :: f (g a) }
data Null a


weaken :: t a -> (h <: t) a
weaken r = Tail r

decomp :: (h <: t) a -> Either (h a) (t a)
decomp (Head h) = Left h
decomp (Tail t) = Right t

absurdU :: Null a -> b
absurdU a = case a of {}

handleUAll
 :: (forall y . (forall x . (x -> b) -> Null x -> b) ->
      (y -> b) ->
      r y -> b)
 -> (a -> b) -> r a -> b
handleUAll f = f (\ _ -> absurdU)

handleU
 :: (forall x . (x -> r) -> h x -> r)
 -> (forall x . (x -> r) -> t x -> r)
 -> (a -> r) -> (h <: t) a -> r
handleU kh kt ka =
  either (kh ka) (kt ka) . decomp

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