{-# LANGUAGE DeriveFunctor, RankNTypes, ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}
module Goat.Co
  ( module Goat.Co
  , module Control.Monad.Free
  )
  where
  
import Control.Monad.Free


-- | Resumable computation
type Comp eff = Free (Co eff)

data Co eff a = forall x . Co (eff x) (x -> a)

instance Functor (Co eff) where
  fmap f (Co r k) = Co r (f . k)
  
-- | Open union
class Sub sub sup where
  inj :: sub a -> sup a

co :: Sub f g => Free (Co f) a -> Free (Co g) b
co (Pure a) = Pure a
co (Free (Co r k)) = Free (Co (inj r) (co . k))

data Sum f g a = InL (f a) | InR (g a)
  
instance Sub f (Sum f g) where inj = InL
instance Sub g (Sum f g) where inj = InR

handleCo
  :: (forall x . f x -> x)
  -> Free (Co (Sum f g)) a -> Free (Co g) a
handleCo kf (Pure a) = Pure a
handleCo kf (Free (Co (InL f) k)) = handleCo kf (k (kf f))
handleCo kf (Free (Co (InR g) k)) = Free (Co g (handleCo kf . k))
