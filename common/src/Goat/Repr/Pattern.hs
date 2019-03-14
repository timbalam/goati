--{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances #-}
module Goat.Repr.Pattern
  where

import Goat.Lang.Ident (Ident)
import Goat.Util (swap, assoc, reassoc)
import Control.Applicative (liftA2)
import Data.These
import Data.Align
import Data.Traversable (mapAccumL)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup
import Data.Void (Void, absurd)

newtype Assoc a = Assoc (Map Ident a)
  deriving (Align, Functor, Foldable, Traversable)

singleton :: Ident -> a -> Assoc a
singleton k a = Assoc (Map.singleton k a)

empty :: Assoc a
empty = Assoc Map.empty

mapWithKey :: (Ident -> a -> b) -> Assoc a -> Assoc b
mapWithKey f (Assoc kv) = Assoc (Map.mapWithKey f kv)

traverseWithKey :: (Ident -> a -> f b) -> Assoc a -> f (Assoc b)
traverseWithKey f (Assoc kv) =
  Assoc <$> Map.traverseWithKey f kv

mapMaybe :: (a -> Maybe b) -> Assoc a -> Assoc b
mapMaybe f (Assoc kv) = Assoc (Map.mapMaybe f kv)

mapEither
 :: (a -> Either b c) -> Assoc a -> (Assoc b, Assoc c)
mapEither f (Assoc ka) = (Assoc kb, Assoc kc)
  where
    (kb, kc) = Map.mapEither f ka

lookup :: Ident -> Assoc a -> Maybe a
lookup k (Assoc kv) = Map.lookup k kv

-- | Associate paths with values, possibly ambiguously
data Paths r a =
    forall x . Node (r x) (x -> Paths r a)
  | Leaf a
  | forall x . Overlap (r x) (x -> Paths r a) a

sendPaths :: r a -> Paths r a
sendPaths r = Node r Leaf

wrapPaths :: r (Paths r a) -> Paths r a
wrapPaths r = Node r id

alignPathsWith
 :: Align r
 => (These a b -> c)
 -> Paths r a -> Paths r b -> Paths r c
alignPathsWith = alignpw where
    alignnw
     :: Align r 
     => (These a b -> c)
     -> r x -> (x -> Paths r a)
     -> r y -> (y -> Paths r b)
     -> (forall xx . r xx -> (xx -> Paths r c) -> p)
     -> p
    alignnw f ra ka rb kb g =
      g (align ra rb) (fmap f . bicrosswalkPaths ka kb)
    
    alignpw
     :: Align r
     => (These a b -> c)
     -> Paths r a -> Paths r b -> Paths r c
    alignpw f (Node ra ka) (Node rb kb) =
      alignnw f ra ka rb kb Node
    alignpw f (Node ra ka) (Leaf b) =
      Overlap ra (fmap (f . This) . ka) (f (That b))
    alignpw f (Node ra ka) (Overlap rb kb b) =
      alignnw f ra ka rb kb Overlap (f (That b))
    alignpw f (Leaf a) (Node rb kb) =
      Overlap rb (fmap (f . That) . kb) (f (This a))
    alignpw f (Leaf a) (Leaf b) =
      Leaf (f (These a b))
    alignpw f (Leaf a) (Overlap rb kb b) =
      Overlap rb (fmap (f . That) . kb) (f (These a b))
    alignpw f (Overlap ra ka a) (Node rb kb)   =
      alignnw f ra ka rb kb Overlap (f (This a))
    alignpw f (Overlap ra ka a) (Leaf b) =
      Overlap ra (fmap (f . This) . ka) (f (These a b))
    alignpw f (Overlap ra ka a) (Overlap rb kb b) =
      alignnw f ra ka rb kb Overlap (f (These a b))

bicrosswalkPaths
 :: Align r 
 => (a -> Paths r c)
 -> (b -> Paths r d)
 -> These a b
 -> Paths r (These c d)
bicrosswalkPaths f g (This a) = This <$> f a
bicrosswalkPaths f g (That b) = That <$> g b
bicrosswalkPaths f g (These a b) = alignPathsWith id (f a) (g b)

instance Functor (Paths r) where
  fmap f (Node r k) = Node r (fmap f . k)
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Overlap r k a) = Overlap r (fmap f . k) (f a)

instance Foldable r => Foldable (Paths r) where
  foldMap f (Node r k) = foldMap (foldMap f . k) r
  foldMap f (Leaf a) =  f a
  foldMap f (Overlap r k a) =
    foldMap (foldMap f . k) r `mappend` f a

instance Traversable r => Traversable (Paths r) where
  traverse f = traverse' f where
    traverseNode
      :: (Traversable r, Applicative f)
      => (a -> f b)
      -> r x -> (x -> Paths r a)
      -> (forall xx . r xx -> (xx -> Paths r b) -> p)
      -> f p
    traverseNode f r k g =
      g <$> traverse (traverse f . k) r <*> pure id
    
    traverse' f (Node r k) =
      traverseNode f r k Node
    traverse' f (Leaf a) = Leaf <$> f a
    traverse' f (Overlap r k a) =
      traverseNode f r k Overlap <*> f a
  
-- | Access controlled labels
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Foldable, Traversable)

bicrosswalkPublic
 :: (a -> Public c)
 -> (b -> Public d)
 -> These a b
 -> Public (These c d)
bicrosswalkPublic f g =
  Public . bimap (getPublic . f) (getPublic . g)

newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable)

bicrosswalkLocal
 :: (a -> Local c)
 -> (b -> Local d)
 -> These a b
 -> Local (These c d)
bicrosswalkLocal f g =
  Local . bimap (getLocal . f) (getLocal . g)
  
newtype Control p r a =
  Control (r (p (Public a) (Local a)))

hoistControl
 :: Functor r 
 => (forall x . p (Public x) (Local x) -> q (Public x) (Local x))
 -> Control p r a -> Control q r a
hoistControl f (Control kv) = Control (fmap f kv)

transControl
 :: (forall x . r x -> s x)
 -> Control p r a -> Control p s a
transControl f (Control kv) = Control (f kv)

instance (Bifunctor p, Functor r) => Functor (Control p r) where
  fmap f (Control r) = Control (fmap (bimap (fmap f) (fmap f)) r)

instance (Bifoldable p, Foldable r) => Foldable (Control p r) where
  foldMap f (Control r) =
    foldMap (bifoldMap (foldMap f) (foldMap f)) r

instance
  (Bitraversable p, Traversable r) => Traversable (Control p r)
  where
    traverse f (Control r) =
      Control <$> traverse (bitraverse (traverse f) (traverse f)) r

instance Align r => Align (Control These r) where
  nil = Control nil
  
  align (Control kva) (Control kvb) =
    Control (alignWith arrange kva kvb) where 
      arrange
       :: These
           (These (Public a) (Local a))
           (These (Public b) (Local b))
       -> These (Public (These a b)) (Local (These a b))
      arrange = 
        bimap
          (bicrosswalkPublic id id)
          (bicrosswalkLocal id id) .
          swapThese
          
      swapThese
       :: These (These a b) (These c d) 
       -> These (These a c) (These b d)
      swapThese = reassoc . first swapThat . assoc
      
      swapThat
       :: These (These a b) c -> These (These a c) b
      swapThat = assoc . second swap . reassoc
      

data Declared p r a =
  forall x . Declared (Control p r x) (x -> Paths r a)

sendDeclared
 :: r (p (Public a) (Local a)) -> Declared p r a
sendDeclared r = Declared (Control r) Leaf

wrapDeclared
 :: r (p (Public (Paths r a)) (Local (Paths r a)))
 -> Declared p r a
wrapDeclared r = Declared (Control r) id

hoistDeclared
 :: Functor r 
 => (forall x . p (Public x) (Local x) -> q (Public x) (Local x))
 -> Declared p r a -> Declared q r a
hoistDeclared f (Declared r k) =
  Declared (hoistControl f r) k

instance Functor (Declared p r) where
  fmap f (Declared r k) = Declared r (fmap f . k)

instance
  (Bifoldable p, Foldable r) => Foldable (Declared p r)
  where
    foldMap f (Declared r k) = foldMap (foldMap f . k) r

instance
  (Bitraversable p, Traversable r) => Traversable (Declared p r)
  where
    traverse f (Declared r k) =
      Declared <$> 
        traverse (traverse f . k) r <*>
        pure id

instance Align r => Align (Declared These r) where
  nil = Declared nil absurd
  
  align (Declared ra ka) (Declared rb kb) =
    Declared
      (align ra rb)
      (bicrosswalkPaths ka kb)

newtype Scopes b f a = Scopes (f (These b a))
  deriving (Functor, Foldable, Traversable)

liftScope
 :: Functor f => f a -> Scopes b f a
liftScope fa = Scopes (that <$> fa)

hoistScopes
 :: Functor f
 => (forall x . f x -> g x)
 -> Scopes b f a -> Scopes b g a
hoistScopes f (Scopes fa) = Scopes (f fa)

alignScopes
 :: Scopes b f a -> f c -> Scopes b f (These a c)
alignScopes (Scopes fba) fc =
  Scopes (alignWith reassoc fba fc)


data Bindings b f p a =
    In (f (NonEmpty a))
  | Let p a (Bindings b (Scopes b f) p a)

hoistBindings
 :: Functor f
 => (forall x . f x -> g x)
 -> Bindings b f p a -> Bindings b g p a
hoistBindings f (In fa) = In (f fa)
hoistBindings f (Let p a sba) =
  Let p a (hoistBindings (hoistScopes f) sba)


instance Functor f => Functor (Bindings b f p) where
  fmap = second

instance Foldable f => Foldable (Bindings b f p) where
  foldMap = bifoldMap (const mempty)

instance Traversable f => Traversable (Bindings b f p)
  where
    traverse = bitraverse pure

instance Functor f => Bifunctor (Bindings b f) where
  bimap f g (In fa) = In (fmap g fa)
  bimap f g (Let p a sba) =
    Let (f p) (g a) (bimap f (fmap g) sba)
  
instance Foldable f => Bifoldable (Bindings b f)
  where
    bifoldMap f g (In fa) = foldMap g fa
    bifoldMap f g (Let p a sba) =
      f p `mappend` g a `mappend` bifoldMap f (foldMap g) sba

instance Traversable f => Bitraversable (Bindings b f)
  where
    bitraverse f g (In fa) = In <$> traverse g fa
    bitraverse f g (Let p a sba) =
      Let <$> f p <*> g a <*> bitraverse f (traverse g) sba

instance Align f => Monoid (Bindings b f p a) where
  mempty = In nil
  
  mappend = mappend' alignWith where
    
  
    mappend'
     :: (f a -> g a -> f (These a a))
     -> Bindings b f p a -> Bindings b g p a -> Bindings b f p a
    mappend' align' (In fa) (In fb) =
      In (these id id (<>) <$> align' f fa fb)
    mappend' align' (Let p a sa) (In fb) =
      Let p a (mappend' alignScopes sa (In fb))
    mappend' (Let p a sa) sb =
      Let p b (mappend' (hoistBindings liftScopes sa) sb)
      

instance Align f => Align (Bindings b f p) where
  nil = In nil
  
  alignWith f = alignWith' f where
    alignIn f = alignWith (fmap (f . swap) . reassoc . swap)
    alignLet f = alignWith (fmap f . reassoc)
    
    alignWith' f (In fa) (In fb) =
      In (alignWith f fa fb)
    alignWith' f (In fa) (Let p c sbc) =
      Let p (f (That c)) (alignIn f (In fa) sbc)
    alignWith' f (Let p a sba) sbc =
      Let p (f (This a)) (alignLet f sba sbc)

type IdxBindings f p = Bindings (NonEmpty Int) f (p ())

crosswalkPattern
 :: (Traversable p, Align f)
 => (a -> Int -> IdxBindings f p Int)
 -> p a -> b -> IdxBindings f p b
crosswalkPattern g pa b =
  Let p' b
    (This <$>
      crosswalkDuplicates id (zipWith g as [0..]))
  where
    (as, p') = mapAccumL (\ as a -> (a:as, ())) [] pa

crosswalkDuplicates
 :: Align f => (a -> f b) -> [a] -> f (NonEmpty b)
crosswalkDuplicates f [] = nil
crosswalkDuplicates f (x:xs) = go x xs where
  go x  []      = fmap pure (f x)
  go x1 (x2:xs) = alignWith cons (f x1) (go x2 xs) where
    cons = these pure id (NonEmpty.<|)

data Pattern r a = Pattern (r a) a
  deriving (Functor, Foldable, Traversable)

newtype Multi r a = Multi (r (NonEmpty a))
  deriving (Functor, Foldable, Traversable)
{-
instance Functor r => Functor (Multi r) where
  fmap f (Multi r) = Multi (fmap (fmap f) r)

instance Foldable r => Foldable (Multi r) where
  foldMap f (Multi r) = foldMap (foldMap f) r

instance Traversable r => Traversable (Multi r) where
  traverse f (Multi r) =
    Multi <$> traverse (traverse f) r <*> pure id
-}
{-
-- | Helper type for manipulating existential continuations
newtype C r a =
  C { runC :: forall y . (forall x . r x -> (x -> a) -> y) -> y }
  
sendC :: r a -> C r a
sendC r = C (\ kf -> kf r id)

hoistC :: (forall x. f x -> g x) -> C f a -> C g a
hoistC f m = runC m (\ r k -> C (\ kf -> kf (f r) k))
  
instance Functor (C r) where
  fmap f m = runC m (\ r k -> C (\ kf -> kf r (f . k)))

instance Foldable r => Foldable (C r) where
  foldMap f m = runC m (\ r k -> foldMap (f . k) r)

instance Traversable r => Traversable (C r) where
  traverse f m = runC m (\ r k -> sendC <$> traverse (f . k) r)

instance Align r => Align (C r) where
  nil = C (\ kf -> kf nil absurd)
  
  align ma mb = C (\ kf ->
    runC ma (\ ra ka ->
    runC mb (\ rb kb ->
      kf (align ra rb) (bimap ka kb))))
-}