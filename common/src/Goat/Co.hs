{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE EmptyCase, TypeOperators, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeFamilies, PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Co
  where

import Control.Monad (ap, liftM)
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

sends :: t x -> (x -> Comp t a) -> Comp t a
sends r k = Req r k

send :: h (Comp (h <: t) a) -> Comp (h <: t) a
send h = sends (Head h) id

iter
  :: (forall x . eff x -> (x -> r) -> r)
  -> (a -> r)
  -> Comp eff a -> r
iter kf ka (Done a) = ka a
iter kf ka (Req r k) = kf r (iter kf ka . k)

handle
 :: (forall x . h x -> (x -> Comp t a) -> Comp t a)
 -> Comp (h <: t) a -> Comp t a
handle f = 
  iter
    (\ r k -> case r of
      Head h -> f h k
      Tail t -> Req t k)
    Done

runComp :: Comp Null a -> a
runComp (Done a) = a

-- | Add an effect to a computation
newtype (m <<: h) t = EComp { getE :: m (h <: t) }

newtype DComp a f = DComp { getD :: Comp f a } 

runDComp :: DComp a Null -> a
runDComp = runComp . getD

-- type Path cmp = Field ((<<:) cmp Chain Null)
-- Chain a = Field a a

-- instance Field_ (Comp (Chain <: t) a) where
--   Compound (Comp (Chain <: t) a) =
--     (Comp (Chain <: t) a)
--   c #. i = send (c :#. i) id

-- instance DSend m => Field_ ((<<:) m Chain t) where
--   Compound ((<<:) m Chain t) = ((<<:) m Chain t)
--   c #. i = EComp (dsend (c :#. i) runEComp)

-- instance Field_ (m (g <: t)) => Field_ ((<<:) m g t) where
--   Compound ((<<:) m g t) = Compound (m (g <: t))
--   c #. i = EComp (c #. i)

class DSend m where
  dsends :: r x -> (x -> m r) -> m r
  
instance DSend (DComp a) where
  dsends r k = DComp (sends r (getD . k))

instance DSend m => DSend (m <<: g) where
  dsends r k = EComp (dsends (Tail r) (getE . k))
  
class DSend m => DIter m where
  diter
   :: (forall x . eff x -> (x -> m t) -> m t)
   -> m eff -> m t

instance DIter (DComp a) where
  diter kf (DComp c) = iter kf (DComp . pure) c
  
instance DIter m => DIter (m <<: h) where
  diter kf (EComp m) = EComp (diter (dkf kf) m)
    -- m :: m (h <: eff)
    -- kf :: eff x -> (x -> r) -> r
    -- diter
    --  :: (forall x . eff x -> (x -> m (h <: t)) -> m (h <: t))
    --  -> m eff -> m (h <: t)
    where
      dkf
        :: DSend m
        => (eff x -> (x -> (m <<: h) t) -> (m <<: h) t)
        -> (h <: eff) x -> (x -> m (h <: t)) -> m (h <: t)
      dkf kf (Head r) k = dsends (Head r) k 
      dkf kf (Tail r) k = getE (kf r (EComp . k))
      -- send :: (h <: t) x -> (x -> m (h <: t)) -> m (h <: t)

dsend
 :: DSend m => h ((m <<: h) t) -> (m <<: h) t
dsend h = EComp (dsends (Head h) getE)


dhandle
 :: DIter m
 => (forall x . h x -> (x -> m t) -> m t)
 -> (m <<: h) t -> m t
dhandle f (EComp m) =
  diter
    (\ r k -> case r of
      Head h -> f h k
      Tail t -> dsends t k)
    m
  -- diter
  --  :: (forall x . (h <: t) x -> (x -> m t) -> m t)
  --  -> m (h <: t) -> m t

class DView (m :: (* -> *) -> *) where
  type DEff m (t :: * -> *) :: * -> *
  type DVal m
  dview :: m t -> Comp (DEff m t) (DVal m)
  dreview :: Comp (DEff m t) (DVal m) -> m t

instance DView (DComp a) where
  type DEff (DComp a) t = t 
  type DVal (DComp a) = a
  dview = getD
  dreview = DComp

instance DView m => DView (m <<: h) where
  type DEff (m <<: h) t = DEff m (h <: t)
  type DVal (m <<: h) = DVal m
  dview = dview . getE
  dreview = EComp . dreview
  
dpure :: DView m => DVal m -> m t
dpure a = dreview (pure a)

dbind
 :: (DView m, DView m', DEff m t ~ DEff m' t)
 => m t -> (DVal m -> m' t) -> m' t
dbind m k = dreview (dview m >>= dview . k)
  