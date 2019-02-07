{-# LANGUAGE DeriveFunctor, DeriveApplicative, DeriveMonad, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE EmptyCase, TypeOperators, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, PolyKinds #-}
module Goat.Co
  ( module Goat.Co
  , module Control.Monad.Free
  )
  where

import Control.Monad (ap, liftM)
import Control.Monad.Free
import Data.Void (absurd)

infixl 1 <<:
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

inj :: Comp t a -> Comp (h <: t) a
inj (Done a) = Done a
inj (Req t k) = Req (Tail t) (inj . k)

send :: h x -> (x -> Comp (h <: t) a) -> Comp (h <: t) a
send r k = Req (Head r) k

handle
 :: (forall x . h x -> (x -> Comp t a) -> Comp t a)
 -> Comp (h <: t) a -> Comp t a 
handle f (Append (Done a)) = Done a
handle f (Append (Req (Head r) k)) = f r (handle f . k)
handle f (Append (Req (Tail r) k)) = Req r (handle f . k)

runComp :: Comp Null a -> a
runComp (Done a) = a

-- | Add an effect to a computation
newtype (m <<: h) t = App { unapp :: m (h <: t) }

newtype FlipComp a f = Flip { unflip :: Comp f a } 

-- type Path cmp = Field ((cmp <<: Chain) Null)
-- Chain a = Field a a

-- instance Field_ ((FlipComp a <<: Chain) t) where
--   Compound ((FlipComp a <<: Chain) t) =
--     ((FlipComp a <<: Chain) t)
--   c #. i = flipsend (c #. i) id

-- instance Field_ (FlipComp a t) => Field_ ((FlipComp a <<: h) t)
--   where
--     Compound ((FlipComp a <<: h) t) = Compound (FlipComp a t)
--     c #. i = flipinj (c #. i)

flipsend :: h ((FlipComp a <<: h) t) -> (FlipComp a <<: h) t
flipsend h = App (Flip (send h id))

flipinj :: FlipComp a t -> (FlipComp a <<: h) t
flipinj (Flip c) = App (Flip (inj c))


