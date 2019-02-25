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
import Data.Void (absurd)


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
        
data Pattern r a =
    forall x . Decomp (r x) (x -> NonEmpty (Pattern r a))
  | Bind a
  | forall x .
      DecompAndBind (r x) (x -> NonEmpty (Pattern r a)) a

instance Functor (Pattern r) where
  fmap f (Decomp r k) = Decomp r (fmap (fmap f) . k)
  fmap f (Bind a) = Bind (f a)
  fmap f (DecompAndBind r k a) =
    DecompAndBind r (fmap (fmap f) . k) (f a)

instance Foldable r => Foldable (Pattern r) where
  foldMap f (Decomp r k) =
    foldMap (foldMap (foldMap f) . k) r
  foldMap f (Bind a) = f a
  foldMap f (DecompAndBind r k a) =
    foldMap (foldMap (foldMap f) . k) r `mappend` f a

instance Traversable r => Traversable (Pattern r) where
  traverse f (Decomp r k) =
    Decomp <$>
      traverse (traverse (traverse f) . k) r <*>
      pure id
  traverse f (Bind a) = Bind <$> f a
  traverse f (DecompAndBind r k a) =
    DecompAndBind <$>
      traverse (traverse (traverse f) . k) r <*>
      pure id <*>
      f a

data Bindings p f a =
    Result (f a)
  | Match (p ()) a (Bindings p f (These (NonEmpty Int) a))

instance Functor f => Functor (Bindings p f) where
  fmap f (Result fa) = Result (fmap f fa)
  fmap f (Match p a sa) =
    Match p (f a) (fmap (fmap f) sa)
  
instance Foldable f => Foldable (Bindings p f)
  where
    foldMap f (Result fa) = foldMap f fa
    foldMap f (Match p a sa) =
      f a `mappend` foldMap (foldMap f) sa

instance Traversable f => Traversable (Bindings p f)
  where
    traverse f (Result fa) = Result <$> traverse f fa
    traverse f (Match p a sa) =
      Match p <$> f a <*> traverse (traverse f) sa

instance Align f => Align (Bindings p f) where
  nil = Result nil
  
  alignWith f = alignWith' f where
    alignWith' f (Result fa) (Result fb) =
      Result (alignWith f fa fb)
    alignWith' f (Result fa) (Match p b sb) =
      Match p (f (That b)) (alignWith (assocWith f) (Result fa) sb)
    alignWith' f (Match p a sa) sb =
      Match p (f (This a)) (alignWith (reassocWith f) sa sb)
      
    reassocWith
     :: (These a b -> c)
     -> These (These (NonEmpty Int) a) b
     -> These (NonEmpty Int) c
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

data Define r f a =
  forall x .
    Define
      (r x)
      (x -> Bindings (Pattern (Define r f)) f (NonEmpty a))

deriving instance Functor f => Functor (Define r f)

instance (Foldable r, Foldable f) => Foldable (Define r f) where
  foldMap f (Define r k) = foldMap (foldMap (foldMap f) . k) r

instance
  (Traversable r, Traversable f) => Traversable (Define r f)
  where
    traverse f (Define r k) =
      Define <$>
        traverse (traverse (traverse f) . k) r <*>
        pure id

instance (Align r, Align f) => Semigroup (Define r f a)
  where
    Define r1 k1 <> Define r2 k2 =
      Define
        (align r1 r2)
        (fmap (these id id (<>)) . bicrosswalk k1 k2)


type IdxBinding r f = Int -> r (f Int)
type IdxPattern r f = Pattern (Define r f) (IdxBinding r f)

definePattern
 :: (Align r, Traversable r, Align f, Traversable f)
 => Pattern (Define r f) (IdxBinding r f) -> a -> Define r f a
definePattern p a =
  crosswalkPattern p (pure a) Define

crosswalkPattern
 :: (Traversable p, Align r, Traversable r, Align f, Traversable f)
 => p (IdxBinding r f)
 -> a
 -> (forall x .
      r x
      -> (x -> Bindings p f a)
      -> s)
 -> s
crosswalkPattern p a f =
  crosswalkPaths
    (zip bs [0..])
    (\ r k -> f r (Match p' a . Result . fmap This . k))
  where
    (bs, p') =
      traverse (\ b -> ([b], ())) p
    
    crosswalkPaths
     :: (Align r, Align f)
     => [(IdxBinding r f, Int)]
     -> (forall x .
          r x -> (x -> f (NonEmpty Int)) -> p)
     -> p
    crosswalkPaths [] = runC nil
    crosswalkPaths (bn:bns) =
      crosswalkMatches (\ (f, n) -> sendC (f n)) (bn:|bns)
      {-
      runC
        (getCompose
          (fmap
            (foldr1 (<>))
            (crosswalkNonEmpty
              (\ (f, n) -> Compose (sendC (f (pure n))))
              (bn:|bns))))
      -}

foldMatches
 :: (Align r, Align f, Semigroup b)
 => (a -> C r (f b))
 -> NonEmpty a
 -> (forall x . r x -> (x -> f b) -> p)
 -> p
foldMatches f ne =
  runC
    (getCompose
      (unwrapAlign
        (foldMap (WrappedAlign . Compose . f) ne)))

crosswalkMatches
 :: (Align r, Align f)
 => (a -> C r (f b))
 -> NonEmpty a
 -> (forall x . r x -> (x -> f (NonEmpty b)) -> p)
 -> p
crosswalkMatches f ne =
  runC (getCompose (crosswalkNonEmpty (Compose . f) ne))

-- missing instance
crosswalkNonEmpty
 :: Align f => (a -> f b) -> NonEmpty a -> f (NonEmpty b)
crosswalkNonEmpty f (x:|[]) = fmap pure (f x)
crosswalkNonEmpty f (x1:|x2:xs) =
  alignWith cons (f x1) (crosswalkNonEmpty f (x2:|xs)) where
    cons = these pure id (NonEmpty.<|) 


-- | Helper type for manipulating existential continuations
newtype C r a =
  C { runC :: forall y . (forall x . r x -> (x -> a) -> y) -> y }
  
sendC :: r a -> C r a
sendC r = C (\ kf -> kf r id)
  
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
