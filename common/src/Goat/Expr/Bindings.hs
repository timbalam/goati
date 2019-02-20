{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Goat.Expr.Bindings
  where

import Goat.Lang.Ident
import Goat.Lang.Let
import Control.Monad (ap, liftM)
import Control.Monad.Free
import Data.Bifunctor
import qualified Data.Map as Map
import Data.Align
import Data.These (mergeTheseWith)
import Data.Void (absurd)


infixr 5 :?

newtype Bindings a = Bindings (Map.Map Ident a)
  deriving (Align, Functor)

singleton :: Ident -> a -> Bindings a
singleton k a = Bindings (Map.singleton k a)

empty :: Bindings a
empty = Bindings Map.empty

data Node r a b =
    Closed a
  | forall x . Open (r x) (x -> b)

instance Bifunctor (Node r) where
  bimap f g (Closed a) = Closed (f a)
  bimap f g (Open r k) = Open r (g . k)

-- | A possibly ambiguous value with two states,
-- a closed / final type 'a' and
-- an open / extensible nested type 'r'.
data Ambig r a b = Node r b (Ambig r a b) :? [a]

send :: r b -> Ambig r a b
send r = Open r pure :? []

instance Functor (Ambig r a) where
  fmap = liftM
  
instance Applicative (Ambig r a) where
  pure = return
  (<*>) = ap

instance Monad (Ambig r a) where
  return a = Closed a :? []
  Closed a :? bs >>= f =
    let n :? bs' = f a in n :? bs' ++ bs
  Open r k :? bs >>= f = Open r ((>>= f) . k) :? bs

instance Bifunctor (Ambig r) where
  bimap f g (n :? as) = bimap g (bimap f g) n :? fmap f as

instance Align r => Semigroup (Ambig r a a) where
  e :? as1 <> Closed a2 :? as2 =
    e :? as1 ++ [a2] ++ as2
  Closed a1 :? as1 <> Open r k :? as2 =
    Open r k :? [a1] ++ as1 ++ as2
  Open r1 k1 :? as1 <> Open r2 k2 :? as2 =
    Open (align r1 r2) (mergeTheseWith k1 k2 (<>)) :? as1 ++ as2


newtype Binding =
  Binding
    (forall a b
      . b -> Bindings (Visibilities (Ambig Bindings a b)))

instance IsString Binding where
  fromString s =
    Binding (singleton (fromString s) . Local . return)

instance Field_ (Binding (Ambig Bindings a)) where
  type Compound (Binding (Ambig Bindings a)) =
    Reference (Binding (Ambig Bindings a))
  Self #. n = Binding (singleton (fromString s) . Public . return)
  Reference (Binding f) #. n =
    Binding (join . f . send . singleton n')

-- | Binder visibility
data Visiblities a b = Public a | Local b | Mixed a b

visibilities
  :: (a -> r) -> (b -> r) -> (r -> r -> r) -> Visibilities a b -> r
visibilities ka kb f (Public a) = ka a 
visibilities ka kb f (Local b) = kb b
visibilities ka kb f (Mixed a b) = f (ka a) (kb b)

instance
  (Semigroup a, Semigroup b) => Semigroup (Visibilities a b)
  where
    Public a1   <> Public a2   = Public (a1 <> a2)
    Public a    <> Local b     = Mixed a b
    Public a1   <> Mixed a2 b  = Mixed (a1 <> a2) b
    Local b     <> Public a    = Mixed a b
    Local b1    <> Local b2    = Local (b1 <> b2)
    Local b1    <> Mixed a b2  = Mixed a (b1 <> b2)
    Mixed a1 b  <> Public a2   = Mixed (a1 <> a2) b
    Mixed a b1  <> Local b2    = Mixed a (b1 <> b2)
    Mixed a1 b1 <> Mixed a2 b2 = Mixed (a1 <> a2) (b1 <> b2)

data Reference a = Self | Reference a

reference :: r -> (a -> r) -> Reference a -> r
reference r f Self = r
reference r f (Reference a) = f a

instance IsString a => IsString (Reference a) where
  fromString "" = Self
  fromString s = Reference (fromString s)

instance Field_ a => Field_ (Reference a) where
    type Compound (Reference a) = Compound a
    m #. k = Reference (m #. k)
    


      
  

