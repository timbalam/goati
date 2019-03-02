--{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances #-}
module Goat.Expr.Pattern
  where

import Goat.Lang.Ident (Ident)
import Goat.Util
  ( Compose(..), WrappedAlign(..), swap, assoc, reassoc )
import Control.Applicative (liftA2)
import Data.These
import Data.Align
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup
import Data.Void (Void, absurd)

infixl 5 :?

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
  | forall x . Overlap (r x) (x -> Path r a) a

sendPath :: r a -> Path r a
sendPath r = Node r Leaf

wrapPath :: r (Path r a) -> Path r a
wrapPath r = Node r id

alignPathWith
 :: Align r
 => (These a b -> c)
 -> Path r a -> Path r b -> Path r c
alignPathWith = alignpw where
    alignnw
     :: Align r 
     => (These a b -> c)
     -> r x -> (x -> Path f a)
     -> r y -> (y -> Path f b)
     -> (forall xx . r xx -> (xx -> Path f c) -> p)
     -> p
    alignnw f ra ka rb kb g =
      g (align ra rb) (fmap f . bicrosswalk ka kb)
      
    alignpw f (Node ra ka) (Node rb kb) =
      alignnw f ra ka rb kb Node
    alignpw f (Node ra ka) (Leaf b) =
      Overlap ra (fmap f . This . ka) (f (That b))
    alignpw f (Node ra ka) (Overlap rb kb b) =
      alignnw f ra ka rb kb Overlap (f (That b))
    alignpw f (Leaf a) (Node rb kb) =
      Overlap rb (fmap f . That . kb) (f (This a))
    alignpw f (Leaf a) (Leaf b) =
      Leaf (f (These a b))
    alignpw f (Leaf a) (Overlap rb kb b) =
      Overlap rb (fmap f . That . kb) (f (These a b))
    alignpw f (Overlap ra ka a) (Node rb kb)   =
      alignnw f ra ka rb kb Overlap (f (This a))
    alignpw f (Overlap ra ka a) (Leaf b) =
      Overlap ra (fmap f . This . ka) (f (These a b))
    alignpw f (Overlap ra ka a) (Overlap rb kb b) =
      alignnw f ra ka rb kb Overlap (f (These a b))

crosswalkPathWith
 :: Align r 
 => (These a b -> c)
 -> These (Path r a) (Path r b)
 -> Path r c
crosswalkPathWith f (This pa) = f . This <$> pa
crosswalkPathWith f (That pb) = f . That <$> pb
crosswalkPathWith f (These pa pb) = alignPathWith f pa pb

instance Functor (Path r) where
  fmap f (Node r k) = Node r (fmap f . k)
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Overlap r k a) = Overlap r (fmap f . k) (f a)

instance Foldable r => Foldable (Path r) where
  foldMap f (Node r k) = foldMap (fmap f . k) r
  foldMap f (Leaf a) =  f a
  foldMap f (Overlap r k a) =
    foldMap (fmap f . k) r `mappend` f a

instance Traversable r => Traversable (Path r) where
  traverse f = traverse' f where
    traverseNode
      :: (Traversable r, Applicative f)
      => (a -> f b)
      -> r x -> (x -> Path r a)
      -> (forall xx . r xx -> (xx -> Path r b) -> p)
      -> f p
    traverseNode f r k g =
      g <$> traverse (traverse f . k) r <*> pure id
    
    traverse' f (Node r k)   =
      traverseNode f r k Node
    traverse' f (Leaf a) = f a
    traverse' f (Overlap r k a) =
      traverseNode f r k Leaf <*> f a
  
-- | Access controlled labels
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Foldable, Traversable)

crosswalkPublicWith
 :: (These a b -> c)
 -> These (Public a) (Public b)
 -> Public c
crosswalkPublicWith f = Public . f . fmap getPublic

newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable)

crosswalkLocalWith
 :: (These a b -> c)
 -> These (Local a) (Local b)
 -> Local c
crosswalkLocalWith f = Local . f . fmap getLocal
  
newtype Control p r a =
  Control (r (p (Public a) (Local a)))

hoistControl
 :: Functor r 
 => (forall x . p (Public x) (Local x) -> p' (Public x) (Local x))
 -> Control p r a -> Control p' r a
hoistControl f (Control kv) = Control (fmap f kv)

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
  
  alignWith f (Control kva) (Control kvb) =
    Control (alignWith (arrangeWith f) kva kvb) where 
      arrangeWith
       :: (These a b -> c)
       -> These
           (These (Public a) (Local a))
           (These (Public b) (Local b))
       -> These (Public c) (Local c)
      arrangeWith f = 
        bimap (crosswalkPublicWith f) (crosswalkLocalWith f) .
          reassoc .
          first (assoc . second swap . reassoc) .
          assoc

data Matches p r a =
  forall x . Matches (Control p r x) (x -> Path r a)

sendMatches :: r (p (Public a) (Local a)) -> Matches p r a
sendMatches = Matches (Control r) Leaf

wrapMatches
 :: r (p (Public (Path r a)) (Local (Path r a))) -> Matches p r a
wrapMatches = Matches (Control r) id

hoistMatches
 :: (forall x . p (Public x) (Local x) -> q (Public x) (Local x))
 -> Matches p r a -> Matches q r a
hoistMatches f (Matches r k) = Matches (hoistControl f r) k

instance Functor (Matches p r) where
  fmap f (Matches r k) = Matches r (fmap f . k)

instance (Bifoldable p, Foldable r) => Foldable (Matches p r) where
  foldMap f (Matches r k) =
    foldMap (foldMap f . k) r

instance
  (Bitraversable p, Traversable r) => Traversable (Matches p r)
  where
    traverse f (Matches r k) =
      Matches <$> 
        traversed (traverse f . k) r <*>
        pure id
        

instance Align r => Align (Matches These r) where
  nil = Matches nil absurd
  
  alignWith f (Matches ra ka) (Matches rb kb) =
    Matches
      (align ra rb)
      (crosswalkPathWith f ka kb)

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
    alignResult f = alignWith (fmap (f . swap) . reassoc . swap)
    alignMatch f = alignWith (fmap f . reassoc)
    
    alignWith' f (Result fa) (Result fb) =
      Result (alignWith f fa fb)
    alignWith' f (Result fa) (Match p c sbc) =
      Match p (f (That c)) (alignResult f (Result fa) sbc)
    alignWith' f (Match p a sba) sbc =
      Match p (f (This a)) (alignMatch f sba sbc)


newtype PatternIndex = Match Int | Remaining Int

type IdxBindings f p = Bindings (NonEmpty PatternIndex) f (p ())

crosswalkPatternWith
 :: (Traversable p, Align f)
 => (a -> Int -> IdxBindings f p PatternIndex)
 -> p a -> b -> IdxBindings f p b
crosswalkPatternWith g pa b =
  Match p' b . fmap This <$>
    crosswalkDuplicates id (zipWith g as [0..])
  where
    (as, p') = traverse (\ a -> ([a], ())) pa

crosswalkDuplicates
 :: Align f => (a -> f b) -> [a] -> f (NonEmpty b)
crosswalkDuplicates f [] = nil
crosswalkDuplicates f (x:xs) = go x xs where
  go x  []      = fmap pure (f x)
  go x1 (x2:xs) = alignWith cons (f x1) (go x2 xs) where
    cons = these pure id (NonEmpty.<|)

data Ambiguous a = a :? NonEmpty a

instance Functor Ambiguous where
  fmap f (a:?as) = f a :? fmap f as

instance Foldable Ambiguous where
  foldMap f (a:?as) = f a `mappend` foldMap f as

instance Traversable Ambiguous where
  traverse f (a:?as) = (:?) <$> f a <*> traverse f as

data Version r a =
    forall x . Edit (r x) (x -> Version r a)
  | New a (Version r a)
  | forall x .
      Revision (r x) (x -> Version r a) a (Version r a)

convertPath
 :: Path r (NonEmpty a)
 -> Version r (Either (Ambiguous (Path r (NonEmpty a))) a)
convertPath (Node r k) = Edit r (convertPath . k)
convertPath (Leaf (a:|[])) = New (Right a) nil
convertPath (Leaf (a1:|a2:as) =
  New (Left (Leaf . pure <$> a1 :? a2 :| as)) nil
convertPath (Overlap r k as) =
  New (Left (Node r k :? fmap (Leaf . pure) as)) nil
  
instance Functor (Version r) where
  fmap f (Edit r k) = Edit r (fmap f . k)
  fmap f (New a vs) = New (f a) (fmap f vs)
  fmap f (Revision r k a vs) =
    Revision r (fmap f . k) (f a) (fmap f vs)

instance Foldable r => Foldable (Version r) where
  foldMap f (Edit r k) = foldMap (foldMap f . k) r
  foldMap f (New a vs) = f a `mappend` foldMap f vs
  foldMap f (Revision r k a vs) =
    foldMap (foldMap f . k) r `mappend` f a `mappend` foldMap f vs

instance Traversable r => Traversable (Version r) where
  traverse f (Edit r k) =
    Edit <$> traverse (traverse f . k) r <*> pure id
  traverse f (New a vs) = New <$> f a <*> traverse f vs
  traverse f (Revision r k a vs) =
    Revision <$>
      traverse (traverse f . k) r <*>
      pure id <*>
      f a <*> 
      traverse f vs

alignVersionWith
 :: Align r
 => (These a b -> c)
 -> Version r a -> Version r b -> Version r c
alignVersionWith f = alignvw f where
  alignnw
   :: (These a b -> c)
   -> r x -> (x -> Version r a)
   -> r y -> (y -> Version r b)
   -> (forall xx . r xx -> (xx -> Version r c) -> d)
   -> d
  alignnw f ra ka rb kb g =
    g (align ra rb) (fmap f . bicrosswalk ka kb)

  alignvw f (Edit ra ka) (Edit rb kb) =
    alignnw f ra ka rb kb Edit
  alignvw f (New a vsa) (Edit rb kb) =
    Revision
      rb
      (fmap (f . That) . kb)
      (f (This a))
      (f . This <$> vsa)
  alignvw f (Revision ra ka a vsa) (Edit rb kb) =
    alignnw f ra ka rb kb Revision (f (This a)) (f . This <$> vsa)
  alignvw f vsa (New b vsb) =
    New (f (That b)) (alignVersionWith f vsa vsb)
  alignwv f vsa (Revision rb kb b vsb) =
    Revision
      rb
      (fmap (f . That) . k)
      (f (That b))
      (alignVersionWith f vsa vsb)

crosswalkVersionWith
 :: Align r 
 => (These a b -> c)
 -> These (Version r a) (Version r b)
 -> Version r c
crosswalkVersionWith f (This vsa) = f . This <$> vsa
crosswalkVersionWith f (That vsb) = f . That <$> vsb
crosswalkVersionWith f (These vsa vsb) = alignVersionWith f vsa vsb

data Pattern p r a =
  forall x . Decomp (Control p r x) (x -> Version r a)

convertPattern
  :: Matches p r (NonEmpty a)
  -> Pattern p r (Either (Ambiguous (Path r (NonEmpty a))) a)
convertPattern (Matches r k) = Pattern r (convertPath . k)

instance Functor (Pattern p r) where
  fmap f (Decomp r k) = Decomp r (fmap f . k)

instance (Bifoldable p, Foldable r) => Foldable (Pattern r) where
  foldMap f (Decomp r k) = foldMap (foldMap f . k) r

instance
  (Bitraversable p, Traversable r) => Traversable (Pattern r) 
  where
    traverse f (Decomp r k) =
      Decomp <$> traverse (traverse f . k) r <*> pure id

instance Align r => Align (Pattern r) where
  nil = Decomp nil absurd
  
  alignWith f (Decomp ra ka) (Decomp rb kb) =
      Decomp (align ka kb) (crosswalkVersionWith f ra rb)

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
