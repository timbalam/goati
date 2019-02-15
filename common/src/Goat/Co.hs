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

newtype Flip t a f = Flip { unflip :: t f a }

fsend
 :: h (Flip Comp a (h <: t)) -> Flip Comp a (h <: t)
fsend h = Flip (sends (Head h) unflip)

finj
 :: Flip Comp a t -> Flip Comp a (h <: t)
finj (Flip m) = Flip (inj m)

fhandle
 :: (forall x . h x -> (x -> Flip Comp a t) -> Flip Comp a t)
 -> Flip Comp a (h <: t) -> Flip Comp a t
fhandle f (Flip m) =
  Flip (handle (\ h k -> unflip (f h (Flip . k))) m)


-- | Add an effect to a computation
newtype (m <<: h) t = Append { unappend :: m (h <: t) }

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
  
instance DSend (Flip Comp a) where
  dsends r k = Flip (sends r (unflip . k))

instance DSend m => DSend (m <<: g) where
  dsends r k = Append (dsends (Tail r) (unappend . k))
  
class DSend m => DIter m where
  diter
   :: (forall x . eff x -> (x -> m t) -> m t)
   -> m eff -> m t

instance DIter (Flip Comp a) where
  diter kf (Flip c) = iter kf (Flip . pure) c
  
instance DIter m => DIter (m <<: h) where
  diter kf (Append m) = Append (diter (dkf kf) m)
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
      dkf kf (Tail r) k = unappend (kf r (Append . k))
      -- send :: (h <: t) x -> (x -> m (h <: t)) -> m (h <: t)

dsend
 :: DSend m => h ((m <<: h) t) -> (m <<: h) t
dsend h = Append (dsends (Head h) unappend)

dhandle
 :: DIter m
 => (forall x . h x -> (x -> m t) -> m t)
 -> (m <<: h) t -> m t
dhandle f (Append m) =
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

instance DView (Flip Comp a) where
  type DEff (Flip Comp a) t = t 
  type DVal (Flip Comp a) = a
  dview = unflip
  dreview = Flip

instance DView m => DView (m <<: h) where
  type DEff (m <<: h) t = DEff m (h <: t)
  type DVal (m <<: h) = DVal m
  dview = dview . unappend
  dreview = Append . dreview
  
dpure :: DView m => DVal m -> m t
dpure a = dreview (pure a)

dbind
 :: (DView m, DView m', DEff m t ~ DEff m' t)
 => m t -> (DVal m -> m' t) -> m' t
dbind m k = dreview (dview m >>= dview . k)

  