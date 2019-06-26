-- | Module of miscellaneous tools

module Goat.Util
  ( (<&>)
  , abstractEither
  , (...)
  , fromLeft
  )
where

import Bound (Scope(..), Var(..))

infixl 1 <&>
infixr 8 ...

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
f ... g = \ a b -> f (g a b) -- (.) . (.)

-- | Missing from earlier version of 'bound' 
abstractEither
 :: Monad m
 => (a -> Either b c) -> m a -> Scope b m c
abstractEither f m
  = Scope
      (m
       >>= \ a
           -> case f a of 
              Left b -> return (B b)
              Right c -> return (F (return c)))

-- | Missing from earlier version of 'base'
fromLeft :: a -> Either a b -> a
fromLeft _ (Left a) = a
fromLeft a _        = a
