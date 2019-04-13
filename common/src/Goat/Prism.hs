{-# LANGUAGE RankNTypes #-}
-- | Code based on 'Data.Union.Prism' from 'union' package.
module Goat.Prism
  ( Prism
  , prism
  , Prism'
  , prism'
  , review
  , preview
  )
  where

import Control.Applicative (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (First(..))
import Data.Profunctor (Profunctor(..), Choice(..))
import Data.Tagged (Tagged(..))

type Prism s t a b =
  forall p f . (Choice p, Applicative f) => p a (f b) -> p s (f t)
type Prism' s a = Prism s s a a

prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta (either pure (fmap bt)) . right' 

prism' :: (a -> s) -> (s -> Maybe a) -> Prism' s a
prism' bs sma = prism bs (\ s -> maybe (Left s) Right (sma s))

-- Tagged a (Identity b) -> Tagged s (Identity t) 
review :: Prism s t a b -> b -> t
review p = runIdentity . unTagged . p . Tagged . Identity

-- (->) a (Const (First a) b) -> (->) s (Const (First a) t)
preview :: Prism s t a b -> s -> Maybe a
preview l = getFirst . getConst . l (Const . First . Just)

-- (->) a (Either a b) -> (->) s (Either a t)
matching :: Prism s t a b -> s -> Either t a
matching l = either Right Left . l Left
