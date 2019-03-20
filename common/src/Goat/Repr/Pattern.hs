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

traverseWithKey
 :: Applicative f => (Ident -> a -> f b) -> Assoc a -> f (Assoc b)
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
  deriving (Functor, Foldable, Traversable, Monoid)

bicrosswalkPublic
 :: (a -> Public c)
 -> (b -> Public d)
 -> These a b
 -> Public (These c d)
bicrosswalkPublic f g =
  Public . bimap (getPublic . f) (getPublic . g)

newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable, Monoid)

bicrosswalkLocal
 :: (a -> Local c)
 -> (b -> Local d)
 -> These a b
 -> Local (These c d)
bicrosswalkLocal f g =
  Local . bimap (getLocal . f) (getLocal . g)
  
newtype Reveal p r a =
  Reveal (r (p (Public a) (Local a)))

hoistReveal
 :: Functor r 
 => (forall x . p (Public x) (Local x) -> q (Public x) (Local x))
 -> Reveal p r a -> Reveal q r a
hoistReveal f (Reveal kv) = Reveal (fmap f kv)

transReveal
 :: (forall x . r x -> s x)
 -> Reveal p r a -> Reveal p s a
transReveal f (Reveal kv) = Reveal (f kv)

instance (Bifunctor p, Functor r) => Functor (Reveal p r) where
  fmap f (Reveal r) = Reveal (fmap (bimap (fmap f) (fmap f)) r)

instance (Bifoldable p, Foldable r) => Foldable (Reveal p r) where
  foldMap f (Reveal r) =
    foldMap (bifoldMap (foldMap f) (foldMap f)) r

instance
  (Bitraversable p, Traversable r) => Traversable (Reveal p r)
  where
    traverse f (Reveal r) =
      Reveal <$> traverse (bitraverse (traverse f) (traverse f)) r

instance Align r => Align (Reveal These r) where
  nil = Reveal nil
  
  align (Reveal kva) (Reveal kvb) =
    Reveal (alignWith arrange kva kvb) where 
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
  forall x . Declared (Reveal p r x) (x -> Paths r a)

sendDeclared
 :: r (p (Public a) (Local a)) -> Declared p r a
sendDeclared r = Declared (Reveal r) Leaf

wrapDeclared
 :: r (p (Public (Paths r a)) (Local (Paths r a)))
 -> Declared p r a
wrapDeclared r = Declared (Reveal r) id

hoistDeclared
 :: Functor r 
 => (forall x . p (Public x) (Local x) -> q (Public x) (Local x))
 -> Declared p r a -> Declared q r a
hoistDeclared f (Declared r k) =
  Declared (hoistReveal f r) k

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


data Bindings f p m a =
    In (f (NonEmpty (m a)))
  | Let p (m a) (Bindings f p (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

hoistBindings
 :: Functor f
 => (forall x . m x -> n x)
 -> Bindings f p m a -> Bindings f p n a
hoistBindings f (In fma) = In (f <$> fma)
hoistBindings f (Let p ma ta) =
  Let p (f ma) (hoistBindings (hoistScope f) ta)

transBindings
 :: (forall x . f x -> g x)
 -> Bindings f p m a -> Bindings g p m a
transBindings f (In fma) = In (f fma)
transBindings f (Let p ma ta) = Let p ma (transBindings f ta)
 
alignBindings
 :: Align f
 => Bindings f p m a
 -> Bindings f p m b
 -> Bindings f p m (Either a b)
alignBindings (In fa) (In fb) =
  In (alignWith mergeNonEmpty fa fb)
  where
    mergeNonEmpty
     :: Functor m
     => These (NonEmpty (m a)) (NonEmpty (m b))
     -> NonEmpty (m (Either a b))
    mergeNonEmpty =
      mergeTheseWith (fmap (fmap Left)) (fmap (fmap Right)) (<>)
alignBindings (Let p ma ta) (In fmb) = Let p (Left <$> ma) tab
  where
    tab = alignBindings ta (hoistBindings lift (In fmb))
    reassocEither
     :: Either (Either b a) c -> Either b (Either a c)
    reassocEither (Left (Left b)) = Left b
    reassocEither (Left (Right a)) = Right (Left a)
    reassocEither (Right c) = Right (Right c)
alignBindings ta (Let p mb tb) = Let p (Right c) tab
  where
    tab = alignBindings (hoistBindings lift ta) tb
    assocEither
     :: Either a (Either b c) -> Either b (Either a c)
    assocEither (Left a) = Right (Left a)
    assocEither (Right (Left b)) = Left b
    assocEither (Right (Right c)) = Right (Right c)

{-
instance (Functor f, Functor m) => Functor (Bindings f p m) where
  fmap f (In fma) = In (fmap (fmap (fmap f)) fma)

instance
  (Foldable f, Foldable m) => Foldable (Bindings f p m)
  where
    foldMap f (In fma) = foldMap (foldMap (foldMap f)) fma
    foldMap f (Let p ma ta) = foldMap f ma `mappend` foldMap f ta

instance
  (Traversable f, Traversable m) => Traversable (Bindings b f p)
  where
    traverse f (In fma) =
      In <$> traverse (traverse (traverse f)) fma
    traverse f (Let p ma ta) =
      Let p <$> traverse f ma <*> traverse f ta

instance Functor f => Bifunctor (Bindings f) where
  bimap f g (In fa) = In (fmap (fmap g) fa)
  bimap f g (Let p a sba) =
    Let (f p) (g a) (bimap f (fmap g) sba)
  
instance Foldable f => Bifoldable (Bindings b f)
  where
    bifoldMap f g (In fa) = foldMap (foldMap g) fa
    bifoldMap f g (Let p a sba) =
      f p `mappend` g a `mappend` bifoldMap f (foldMap g) sba

instance Traversable f => Bitraversable (Bindings b f)
  where
    bitraverse f g (In fa) = In <$> traverse (traverse g) fa
    bitraverse f g (Let p a sba) =
      Let <$> f p <*> g a <*> bitraverse f (traverse g) sba
-}

instance Functor f => Bound (Bindings f p) where
  In fma      >>>= f = In (fmap (>>= f) fma)
  Let p ma ta >>>= f = Let p (ma >>= f) (ta >>>= f)

instance Align f => Monoid (Bindings f p m a) where
  mempty = In nil
  mappend a b = either id id <$> alignBindings a b
      
{-
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
-}

iterPaths
 :: Monoid b
 => (a -> b) -> (r x -> (x -> b) -> b) -> Paths r a -> b
iterPaths = iterPaths' where
  iterPaths' ka kf (Leaf a) = ka a
  iterPaths' ka kf (Node r k) = iterNode ka kf r k
  iterPaths' ka kf (Overlap r k a) =
    mappend (iterNode ka kf r k) (ka a)
  
  iterNode ka kf r k b = kf r (iterPaths ka kf . k)

patternDeclared
 :: MonadBlock (Abs Assoc Components) m
 => Declared
      These
      Paths
      Assoc
      (Int -> g (Bindings f (Assoc (g ())) m a))
 -> (m a -> g (Bindings f (Assoc (g ())) m a))
 -> m a -> g (Bindings f (Assoc (g ())) m a)
patternDeclared (Declared (Control r) k) f =
  where
  
    (m, v) =
      foldNode r (toComponent (patternPaths . k)) (,) b
      where
        toComponent k =
          mergeTheseWith
            (\ (Public a) b -> first (foldMap public) (k a b))
            (\ (Local a) b -> first (foldMap local) (k a b))
            mappend
        
    
    
patternPaths
 :: (Align f, Alternative g, MonadBlock (Abs Assoc g) m, Monoid c)
 => Paths Assoc (Int -> g (Bindings f (Assoc (g ())) m Int))
 -> Int
 -> (g (Bindings f (Assoc (g ())) m Int ->
         Bindings f (Assoc (g ())) m Int) ->
      Maybe (m Int) ->
      r)
 -> r
patternPaths =
  iterPaths
    (\ f i p -> p (mappend <$> f i) Nothing)
    (\ r k b p -> foldNode r k b (\ a b -> p (pure a) (Just b)))
      

foldNode
 :: (Align f, Alternative g, Monoid c)
 => Assoc a
 -> (a ->
      Int ->
      (forall m .
        MonadBlock (Abs Assoc g) m =>
        g (Bindings f (Assoc (g ())) m b -> c) ->
        Maybe (m Int) ->
        r) ->
      r)
 -> b
 -> (forall m .
      MonadBlock (Abs Assoc g) m =>
      (Bindings f (Assoc (g ())) m b -> c) ->
      m d
      -> r)
 -> r
foldNode r k b p = p m rem
  where
    (m, Pattern rmb mb) =
      foldPattern
        (\ i f -> f i (,))
        (Pattern
          (k <$> r)
          (\ i p -> p (pure mempty) (Just (return i))))
        b
      
    rem = 
      lift
        (wrapBlock
          (Abs
            (Defined
              (Pattern
                (mapMaybe (fmap (pure . lift)) rmb)
                (maybe empty (pure . lift) mb)))))
        >>= Scope . return . B

foldPattern
 :: (Align f, Traversable r, Traversable g, Monoid c)
 => (a ->
      Int ->
      (g (Bindings f (r (g ())) m b -> c), d)
 -> r a
 -> b
 -> (Bindings f (r (g ())) (Scope (Local Int) m) b -> c, r d)
foldPattern k r b =
  (pure (m . Let pg (return b)),  rc)
  where
    (m, pg) = traverse (traverse (\ m -> (m, ()))) rgm
    (rgm, rc) = sequenceBia (mapWithIndex (\ i a -> k a i) r)
    --abstractBindings b =
    --  hoistBindings lift b >>>= Scope . return . B

mapWithIndex
 :: Traversable t
 => (Int -> a -> b) -> t a -> t b
mapWithIndex f t =
  snd (mapAccumL (\ i a -> (i+1, f i a)) 0 t)
  

data Components f a = Public (f a) :? Local (f a)
  deriving (Functor, Foldable, Traversable)

public :: Alternative f => a -> Components f a
public a = Public (pure a) :? Local empty

local :: Alternative f => a -> Components f a
local a = Public empty :? Local (pure a)

instance Alternative f => Applicative (Components f) where
  pure = public 
  Public f1 :? Local f2 <*> Public a1 :? Local a2 =
    Public (f1 <*> a1) :? Local (f2 <*> a2)

instance Alternative f => Alternative (Components f) where
  empty = Public empty :? Local empty
  Public f1 :? Local f2 <|> Public g1 :? Local g2 =
    Public (f1 <|> g1) :? Local (f2 <|> g2)

instance Monoid (f a) => Monoid (Components f a) where
  mempty = mempty :? mempty
  mappend (a1 :? b1) (a2 :? b2) = mappend a1 a2 :? mappend b1 b2
{-
crosswalkDuplicates
 :: Align f => (a -> f b) -> [a] -> f (NonEmpty b)
crosswalkDuplicates f [] = nil
crosswalkDuplicates f (x:xs) = go x xs where
  go x  []      = fmap pure (f x)
  go x1 (x2:xs) = alignWith cons (f x1) (go x2 xs) where
    cons = these pure id (NonEmpty.<|)
-}

data Pattern r a = Pattern (r a) a
  deriving (Functor, Foldable, Traversable)

hoistPattern
 :: (forall x . f x -> g x) -> Pattern f a -> Pattern g a
hoistPattern f (Pattern r a) = Pattern (f r) a

instance (Monoid (r a), Monoid a) => Monoid (Pattern r a) where
  mempty = Pattern mempty mempty
  Pattern r1 a1 `mappend` Pattern r2 a2 =
    Pattern (r1 `mappend` r2) (a1 `mappend` a2)
{-
instance Functor r => Bifunctor (Pattern r) where
  bimap f g (Pattern ra b) = Pattern (fmap f ra) (g b)

instance Foldable r => Bifoldable (Pattern r) where
  bifoldMap f g (Pattern ra b) = foldMap f ra `mappend` g b

instance Traversable r => Bitraversable (Pattern r) where
  bitraverse f g (Pattern ra b) =
    Pattern <$> traverse f ra <*> g b
-}
newtype Multi r a = Multi { getMulti :: r (NonEmpty a) }
  deriving (Functor, Foldable, Traversable)

instance Align r => Monoid (Multi r a) where
  mempty = Multi nil
  mappend (Multi a) (Multi b) =
    Multi (alignWith (these id id (<>)) a b)

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