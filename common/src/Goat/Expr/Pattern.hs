--{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances #-}
module Goat.Expr.Pattern
  where

import Goat.Lang.Ident (Ident)
import Goat.Util (Compose(..), WrappedAlign(..))
import Control.Applicative (liftA2)
import Data.These
import Data.Align
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


newtype Label a = Label (Map Ident a)
  deriving (Align, Functor, Foldable, Traversable)

lsingleton :: Ident -> a -> Label a
lsingleton k a = Label (Map.singleton k a)

lempty :: Label a
lempty = Label Map.empty

lvalues :: Label a -> [(Ident, a)]
lvalues (Label kv) = Map.assocs kv

llookup :: Ident -> Label a -> Maybe a
llookup k (Label kv) = Map.lookup k kv


-- | Associate paths with values, possibly ambiguously
data Path r a =
    forall x . Node (r x) (x -> Path r a)
  | Leaf a
  | forall x . NodeAndLeaf (r x) (x -> Path r a) a

sendPath :: r a -> Path r a
sendPath r = Node r Leaf

wrapPath :: r (Path r a) -> Path r a
wrapPath r = Node r id

instance Functor (Path r) where
  fmap f (Node r k) = Node r (fmap f . k)
  fmap f (Leaf a) = Leaf (f a)
  fmap f (NodeAndLeaf r k a) = NodeAndLeaf r (fmap f . k) (f a)

instance Align r => Align (Path r) where
  nil = Node nil absurd
  
  alignWith f = align' f where
    alignNodes
     :: Align r 
     => r x -> (x -> Path r a)
     -> r y -> (y -> Path r b)
     -> (forall xx . r xx -> (xx -> Path r (These a b)) -> p)
     -> p
    alignNodes ra ka rb kb f =
      f (align ra rb) (bicrosswalk ka kb)
      
    align' f (Node ra ka)          (Node rb kb)          =
      f <$> alignNodes ra ka rb kb Node
    align' f (Node ra ka)          (Leaf b)              =
      NodeAndLeaf ra (fmap (f . This) . ka) (f (That b))
    align' f (Node ra ka)          (NodeAndLeaf rb kb b) =
      f <$> alignNodes ra ka rb kb NodeAndLeaf (That b)
    align' f (Leaf a)              (Node rb kb)          =
      NodeAndLeaf rb (fmap (f . That) . kb) (f (This a))
    align' f (Leaf a)              (Leaf b)              =
      Leaf (f (These a b))
    align' f (Leaf a)              (NodeAndLeaf rb kb b) =
      NodeAndLeaf rb (fmap (f . That) . kb) (f (These a b))
    align' f (NodeAndLeaf ra ka a) (Node rb kb)          =
      f <$> alignNodes ra ka rb kb NodeAndLeaf (This a)
    align' f (NodeAndLeaf ra ka a) (Leaf b)              =
      NodeAndLeaf ra (fmap (f . This) . ka) (f (These a b))
    align' f (NodeAndLeaf ra ka a) (NodeAndLeaf rb kb b) =
      f <$> alignNodes ra ka rb kb NodeAndLeaf (These a b)

instance Foldable r => Foldable (Path r) where
  foldMap f (Node r k) = foldMap (foldMap f . k) r
  foldMap f (Leaf a) = f a
  foldMap f (NodeAndLeaf r k a) =
    foldMap (foldMap f . k) r `mappend` f a

instance Traversable r => Traversable (Path r) where
  traverse f = traverse' where
    traverseNode
      :: (Traversable r, Applicative f)
      => (a -> f b)
      -> r x -> (x -> Path r a)
      -> (forall xx . r xx -> (xx -> Path r b) -> p)
      -> f p
    traverseNode f r k g =
      g <$> traverse (traverse f . k) r <*> pure id
    
    traverse' (Node r k)          =
      traverseNode f r k Node
    traverse' (Leaf a)              =
      fmap Leaf (f a)
    traverse' (NodeAndLeaf r k a) =
      traverseNode f r k NodeAndLeaf <*> f a
  
-- | Access controlled labels
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Foldable, Traversable)

newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable)
  
newtype Control p a =
  Control (Label (p (Public a) (Local a)))

cempty :: Control p a
cempty = Control lempty

csingleton
 :: Ident -> Either (Public a) (Local a) -> Control Either a
csingleton k v = Control (lsingleton k v)

choist
 :: (forall x . p (Public x) (Local x) -> p' (Public x) (Local x))
 -> Control p a -> Control p' a
choist f (Control kv) = Control (fmap f kv)

cpartition
 :: Control Either a -> (Public (Label a), Local (Label a))
cpartition (Control (Label kv)) =
  bimap
    (Public . Label)
    (Local . Label)
    (Map.mapEither (bimap getPublic getLocal) kv)

instance Bifunctor p => Functor (Control p) where
  fmap f (Control kv) =
    Control (fmap (bimap (fmap f) (fmap f)) kv)

instance Bifoldable p => Foldable (Control p) where
  foldMap f (Control kv) =
    foldMap (bifoldMap (foldMap f) (foldMap f)) kv

instance
  Bitraversable p => Traversable (Control p)
  where
    traverse f (Control kv) =
      Control <$> 
        traverse (bitraverse (traverse f) (traverse f)) kv

instance Align (Control These) where
  nil = cempty
  
  alignWith f (Control kva) (Control kvb) =
    Control (alignWith crosswalk' kva kvb)
    where
      crosswalk' =
        these
          (bimap (fmap (f . This)) (fmap (f . This)))
          (bimap (fmap (f . That)) (fmap (f . That)))
          (align' f)

      align' 
       :: (These a b -> c)
       -> These (Public a) (Local a)
       -> These (Public b) (Local b)
       -> These (Public c) (Local c)
      align' f (This (Public a)) (This (Public b)) =
        This (Public (f (These a b)))
      align' f (That (Local a)) (This (Public b)) =
        These (Public (f (That b))) (Local (f (This a)))
      align' f (These (Public a1) (Local a2)) (This (Public b)) =
        These (Public (f (These a1 b))) (Local (f (This a2)))
      align' f (This (Public a)) (That (Local b)) =
        These (Public (f (This a))) (Local (f (That b)))
      align' f (That (Local a)) (That (Local b)) =
        That (Local (f (These a b)))
      align' f (These (Public a1) (Local a2)) (That (Local b)) =
        These (Public (f (This a1))) (Local (f (These a2 b)))
      align' f (This (Public a)) (These (Public b1) (Local b2)) =
        These (Public (f (These a b1))) (Local (f (That b2)))
      align' f (That (Local a)) (These (Public b1) (Local b2)) =
        These (Public (f (That b1))) (Local (f (These a b2)))
      align'
        f
        (These (Public a1) (Local a2))
        (These (Public b1) (Local b2)) =
        These (Public (f (These a1 b1))) (Local (f (These a2 b2)))

data Bindings b f p a =
    Result (f a)
  | Match p a (Bindings b f p (These b a))

hoistBindings
 :: Functor f
 => (forall x . f x -> g x)
 -> Bindings b f p a -> Bindings b g p a
hoistBindings f (Result fa) = Result (f fa)
hoistBindings f (Match p a sba) = Match p a (hoistBindings f sba)

instance Functor f => Functor (Bindings b f p) where
  fmap = second

instance Foldable f => Foldable (Bindings b f p) where
  foldMap = bifoldMap (const mempty)

instance Traversable f => Traversable (Bindings b f p)
  where
    traverse = bitraverse pure

instance Functor f => Bifunctor (Bindings b f) where
  bimap f g (Result fa) = Result (fmap g fa)
  bimap f g (Match p a sba) =
    Match (f p) (g a) (bimap f (fmap g) sba)
  
instance Foldable f => Bifoldable (Bindings b f)
  where
    bifoldMap f g (Result fa) = foldMap g fa
    bifoldMap f g (Match p a sba) =
      f p `mappend` g a `mappend` bifoldMap f (foldMap g) sba

instance Traversable f => Bitraversable (Bindings b f)
  where
    bitraverse f g (Result fa) = Result <$> traverse g fa
    bitraverse f g (Match p a sba) =
      Match <$> f p <*> g a <*> bitraverse f (traverse g) sba

instance Align f => Align (Bindings b f p) where
  nil = Result nil
  
  alignWith f = alignWith' f where
    alignWith' f (Result fa) (Result fb) =
      Result (alignWith f fa fb)
    alignWith' f (Result fa) (Match p c sbc) =
      Match p (f (That c)) (alignWith (assocWith f) (Result fa) sbc)
    alignWith' f (Match p a sba) sbc =
      Match p (f (This a)) (alignWith (reassocWith f) sba sbc)
    
    reassocWith
     :: (These a c -> d)
     -> These (These b a) c
     -> These b d
    reassocWith f =
      assocWith (f . swap) . swap
    
    assocWith
      :: (These a c -> d)
      -> These a (These b c)
      -> These b d
    assocWith f (This a) = That (f (This a))
    assocWith f (That (This b)) = This b
    assocWith f (That (That c)) = That (f (That c))
    assocWith f (That (These b c)) = These b (f (That c))
    assocWith f (These a (This b)) = These b (f (This a))
    assocWith f (These a (That c)) = That (f (These a c))
    assocWith f (These a (These b c)) = These b (f (These a c))
    
    swap :: These a b -> These b a
    swap (This a) = That a
    swap (That b) = This b
    swap (These a b) = These b a

data Pattern r f a =
    forall x . Decomp (r x) (x -> f a)
  | forall x . DecompAndBind (r x) (x -> f a) a

instance Functor f => Functor (Pattern r f) where
  fmap f (Decomp r k) = Decomp r (fmap f . k)
  fmap f (DecompAndBind r k a) = DecompAndBind r (fmap f . k) (f a)

instance (Foldable r, Foldable f) => Foldable (Pattern r f) where
  foldMap f (Decomp r k) = foldMap (foldMap f . k) r
  foldMap f (DecompAndBind r k a) =
    foldMap (foldMap f . k) r `mappend` f a

instance
  (Traversable r, Traversable f) => Traversable (Pattern r f)
  where
    traverse f (Decomp r k) =
      Decomp <$> traverse (traverse f . k) r <*> pure id
    traverse f (DecompAndBind r k a) =
      DecompAndBind <$>
        traverse (traverse f . k) r <*>
        pure id <*>
        f a

type IdxBindings f p = Bindings (NonEmpty Int) f (p ())

crosswalkPatternWith
 :: (Traversable p, Align r, Align f)
 => (a -> Int -> C r (IdxBindings f p Int))
 -> p a
 -> b
 -> C r (IdxBindings f p b)
crosswalkPatternWith g pa b =
  Match p' b . fmap This <$> crosswalkPaths (zipWith g as [0..])
  where
    (as, p') =
      traverse (\ a -> ([a], ())) pa
    
    crosswalkPaths
     :: (Align r, Align f)
     => [C r (IdxBindings f p Int)]
     -> C r (IdxBindings f p (NonEmpty Int))
    crosswalkPaths [] = nil
    crosswalkPaths (bn:bns) =
      crosswalkMatches id (bn:|bns)

crosswalkMatches
 :: (Align r, Align f)
 => (a -> C r (f b))
 -> NonEmpty a
 -> C r (f (NonEmpty b))
crosswalkMatches f ne =
  getCompose (crosswalkNonEmpty (Compose . f) ne)

-- missing instance
crosswalkNonEmpty
 :: Align f => (a -> f b) -> NonEmpty a -> f (NonEmpty b)
crosswalkNonEmpty f (x:|[]) = fmap pure (f x)
crosswalkNonEmpty f (x1:|x2:xs) =
  alignWith cons (f x1) (crosswalkNonEmpty f (x2:|xs)) where
    cons = these pure id (NonEmpty.<|) 


newtype Redefine b p f a =
  Redefine (Bindings b f (p (Redefine b p f) ()) (NonEmpty a))
  deriving (Functor, Foldable, Traversable)

newtype Define f a = Define (f (NonEmpty a))
  deriving (Functor, Foldable, Traversable)


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
