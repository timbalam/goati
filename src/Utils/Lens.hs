
{-# LANGUAGE Rank2Types #-}
module Utils.Lens
where
import Control.Applicative
  ( Const(..)
  )
import Data.Functor.Identity
  ( Identity(..)
  )

-- Lens' s b . Lens' b a = Lens' s a
-- ((b -> f b) -> s -> f s) . ((a -> f a) -> b -> f b) = (a -> f a) -> s -> f s
type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s

lens :: (s -> a) -> (s -> a -> s) -> Lens' s a
lens get set f s = set s `fmap` f (get s)

view :: Lens' s a -> s -> a
view lens = getConst . lens Const

type Setter' s a = (a -> Identity a) -> s -> Identity s 

sets :: ((a -> a) -> s -> s) -> Setter' s a 
sets f g = Identity . f (runIdentity . g)

over :: Setter' s a -> (a -> a) -> s -> s
over lens f = runIdentity . lens (Identity . f)

set :: Setter' s a -> a -> s -> s
set lens b = runIdentity . lens (\_ -> Identity b)