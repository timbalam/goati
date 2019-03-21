--{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Goat.Repr.Pattern
  where

import Goat.Lang.Ident (Ident)
import Goat.Util (swap, assoc, reassoc)
import Bound
import Bound.Scope
import Control.Applicative (liftA2, Alternative(..))
import Control.Monad.Trans (lift)
import Control.Monad.Cont (cont, runCont)
import Data.These
import Data.Align
import Data.Traversable (mapAccumL)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Biapplicative
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Semigroup
import Data.Monoid (Alt(..))
import Data.Void (Void, absurd)

newtype Assoc a = Assoc (Map Ident a)
  deriving (Align, Functor, Foldable, Traversable)

singleton :: Ident -> a -> Assoc a
singleton k a = Assoc (Map.singleton k a)

--empty :: Assoc a
--empty = Assoc Map.empty

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
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)
newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)
newtype Match a = Match { getMatch :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)

newtype Tag s a = Tag (s, a)
  deriving
    ( Functor, Foldable, Traversable, Monoid
    , Bifunctor, Bifoldable, Biapplicative
    )
    
instance Bitraversable Tag where
  bitraverse f g (Tag (s, a)) = Tag <$> ((,) <$> f s <*> g a)

bicrosswalkTag
 :: Semigroup s
 => (a -> Tag s c)
 -> (b -> Tag s d)
 -> These a b
 -> Tag s (These c d)
bicrosswalkTag f g (This a) = This <$> f a
bicrosswalkTag f g (That b) = That <$> g b
bicrosswalkTag f g (These a b) =
  bipure (<>) These <<*>> (f a) <<*>> (g b)

newtype Reveal r s a = Reveal (r (Tag s a))
  deriving (Functor, Foldable, Traversable)

hoistReveal
 :: (forall x . r x -> r' x)
 -> Reveal r s a -> Reveal r' s a
hoistReveal f (Reveal kv) = Reveal (f kv)

instance Functor r => Bifunctor (Reveal r) where
  bimap f g (Reveal r) = Reveal (bimap f g <$> r)

instance Foldable r => Bifoldable (Reveal r) where
  bifoldMap f g (Reveal r) = foldMap (bifoldMap f g) r

instance Traversable r => Bitraversable (Reveal r) where
  bitraverse f g (Reveal r) =
    Reveal <$> traverse (bitraverse f g) r

instance (Align r, Semigroup s) => Align (Reveal r s) where
  nil = Reveal nil
  
  align (Reveal kva) (Reveal kvb) =
    Reveal (alignWith (bicrosswalkTag id id) kva kvb) where

data Declared r s a =
  forall x . Declared (Reveal r s x) (x -> Paths r a)

sendDeclared
 :: r (Tag s a) -> Declared r s a
sendDeclared r = Declared (Reveal r) Leaf

wrapDeclared
 :: r (Tag s (Paths r a)) -> Declared r s a
wrapDeclared r = Declared (Reveal r) id

instance Functor (Declared r s) where
  fmap f (Declared r k) = Declared r (fmap f . k)
  
instance Functor r => Bifunctor (Declared r) where
  bimap f g (Declared r k) =
    Declared (first f r) (fmap g . k)

instance Foldable r => Foldable (Declared r s)
  where
    foldMap f (Declared r k) = foldMap (foldMap f . k) r

instance Traversable r => Traversable (Declared r s)
  where
    traverse f (Declared r k) =
      Declared <$> 
        traverse (traverse f . k) r <*>
        pure id

instance (Align r, Semigroup s) => Align (Declared r s) where
  nil = Declared nil absurd
  
  align (Declared ra ka) (Declared rb kb) =
    Declared
      (align ra rb)
      (bicrosswalkPaths ka kb)

-- Bindings p r m a =
--   In (r m a) | Let p (m a) (Bindings p r (Scope (Local Int) m) a)
data Bindings f p m a =
    In (f (NonEmpty (m a)))
  | Let p (m a) (Bindings f p (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

hoistBindings
 :: (Functor f, Functor m)
 => (forall x . m x -> n x)
 -> Bindings f p m a -> Bindings f p n a
hoistBindings f (In fma) = In (fmap f <$> fma)
hoistBindings f (Let p ma ta) =
  Let p (f ma) (hoistBindings (hoistScope f) ta)

transBindings
 :: (forall x . f x -> g x)
 -> Bindings f p m a -> Bindings g p m a
transBindings f (In fma) = In (f fma)
transBindings f (Let p ma ta) = Let p ma (transBindings f ta)
 
alignBindings
 :: (Align f, Monad m)
 => (a -> c)
 -> (b -> c)
 -> Bindings f p m a
 -> Bindings f p m b
 -> Bindings f p m c
alignBindings f g (In fa) (In fb) =
  In (alignWith (mergeNonEmpty f g) fa fb)
  where
    mergeNonEmpty
     :: Functor m
     => (a -> c)
     -> (b -> c)
     -> These (NonEmpty (m a)) (NonEmpty (m b))
     -> NonEmpty (m c)
    mergeNonEmpty f g =
      mergeTheseWith (fmap (fmap f)) (fmap (fmap g)) (<>)
alignBindings f g (Let p ma ta) (In fmb) = Let p (f <$> ma) tab
  where
    tab = alignBindings f g ta (hoistBindings lift (In fmb))
alignBindings f g ta (Let p mb tb) = Let p (g <$> mb) tab
  where
    tab = alignBindings f g (hoistBindings lift ta) tb

instance Functor f => Bound (Bindings f p) where
  In fma      >>>= f = In (fmap (>>= f) <$> fma)
  Let p ma ta >>>= f = Let p (ma >>= f) (ta >>>= lift . f)

instance (Align f, Monad m) => Monoid (Bindings f p m a) where
  mempty = In nil
  mappend a b = alignBindings id id a b

iterPaths
 :: Monoid b
 => (a -> b) -> (forall x . r x -> (x -> b) -> b) -> Paths r a -> b
iterPaths = iterPaths' where
  iterPaths'
   :: Monoid b
   => (a -> b)
   -> (forall x . r x -> (x -> b) -> b)
   -> Paths r a -> b
  iterPaths' ka kf (Leaf a) = ka a
  iterPaths' ka kf (Node r k) = iterNode ka kf r k
  iterPaths' ka kf (Overlap r k a) =
    mappend (iterNode ka kf r k) (ka a)
  
  iterNode
   :: Monoid b
   => (a -> b)
   -> (forall x . r x -> (x -> b) -> b)
   -> r y
   -> (y -> Paths r a)
   -> b
  iterNode ka kf r k = kf r (iterPaths ka kf . k)

type Matchings f r g = Bindings f (Pattern r (g ()))
  
patternDeclared
 :: ( Align f, Traversable t
    , Alternative g, Traversable g, Monoid s
    , MonadBlock (Abs Assoc (Components g s)) m
    )
 => Declared
      Assoc
      s
      (t (m Int -> Matchings f Assoc (Components g s) m Int))
 -> (m Int -> Matchings f Assoc (Components g s) m Int)
 -> m Int -> Matchings f Assoc (Components g s) m Int
patternDeclared (Declared (Reveal r) k) f mi =
  foldNode
    -- Assoc (Tag s a)
    r
    -- Tag s a -> Int ->
    --   ((Maybe (m Int), Components g s ()) -> r) -> r 
    (toComponent
      -- a -> Int -> ((Maybe (m Int), t ()) -> r) -> r
      (\ a i ->
        -- ((Maybe (m Int), t ()) -> r) -> r
        patternPaths
          -- Paths Assoc (m Int -> t r)
          (sequenceA <$> k a)
          (return i)))
    -- m a
    mi
    -- m Int -> r
    f
  where
    toComponent
     :: (Foldable t, Alternative f)
     => (a -> b -> ((d, t ()) -> r) -> r)
     -> Tag s a -> b -> ((d, Components f s ()) -> r) -> r
    toComponent k ta b = runCont (do
      Tag (s, (d, t)) <- traverse (\ a -> cont (k a b)) ta
      let f = getAlt (foldMap pure t)
      return (d, Components (Tag (s, f))))

patternPaths
 :: (Align f, Foldable t, Alternative g, Traversable g
    , MonadBlock (Abs Assoc g) m
    )
 => Paths
      Assoc
      (m Int -> t (Matchings f Assoc g m Int))
 -> m Int
 -> ((Maybe (m Int), g ()) -> Matchings f Assoc g m Int)
 -> Matchings f Assoc g m Int
patternPaths =
  iterPaths
    (\ k a -> remake (k a))
    (\ r k a f ->
      foldNode
        r
        (\ a i -> k a (return i))
        a
        (\ mi -> f (Just mi, pure ())))
  where
    remake
     :: (Foldable t, Alternative g, Monoid m)
     => t m -> ((Maybe a, g ()) -> m) -> m
    remake tm f = f (Nothing, g') `mappend` m
      where
        (m, Alt g') = foldMap (\ m -> (m, pure ())) tm

foldNode
 :: ( Align f, Alternative g, Traversable g
    , MonadBlock (Abs Assoc g) m
    )
 => Assoc a
 -> (a ->
      Int ->
      ((Maybe (m Int), g ()) -> Matchings f Assoc g m b) ->
      Matchings f Assoc g m b)
 -> m b
 -> (m Int -> Matchings f Assoc g m Int)
 -> Matchings f Assoc g m b
foldNode r k b f =
  foldPattern
    id
    (Pattern
      (k <$> r)
      (\ i f -> f (Just (return i), empty)))
    b
    bindPattern
  where
    bindPattern (Pattern rmb mb) =
      hoistBindings
        lift
        (f (makeRemaining rmb mb))
        >>>= Scope . return . B . Local
      where
        makeRemaining
         :: (Alternative f, MonadBlock (Abs Assoc f) m)
         => Assoc (Maybe (m a)) -> Maybe (m a) -> m a
        makeRemaining rmb mb = 
          wrapBlock
            (Abs
              (Defined
                (Pattern
                  (mapMaybe (fmap (pure . lift)) rmb)
                  (maybe empty (pure . lift) mb))))

foldPattern
 :: (Align f, Traversable r, Traversable g, Monad m)
 => (a ->
      Int ->
      ((d, g ()) -> Bindings f (r (g ())) m b) ->
      Bindings f (r (g ())) m b)
 -> r a
 -> m b
 -> (r d -> Bindings f (r (g ())) (Scope (Local Int) m) b)
 -> Bindings f (r (g ())) m b
foldPattern k r b f = traverse cont rc `runCont` makeBindings
  where
    makeBindings rdg = Let pg b (f rd)
      where
        rd = fst <$> rdg
        pg = snd <$> rdg
    
    rc = mapWithIndex (\ i a -> k a i) r    

mapWithIndex
 :: Traversable t
 => (Int -> a -> b) -> t a -> t b
mapWithIndex f t =
  snd (mapAccumL (\ i a -> (i+1, f i a)) 0 t)  

newtype Components f s a = Components (Tag s (f a)) 
  deriving (Functor, Foldable, Traversable)
  
instance Functor f => Bifunctor (Components f) where
  bimap f g (Components tsfa) = Components (bimap f (fmap g) tsfa)

instance Applicative f => Biapplicative (Components f) where
  bipure s a = Components (bipure s (pure a))
  Components tgfh <<*>> Components tsfa =
    Components (fmap (<*>) tgfh <<*>> tsfa)
    
instance
  (Applicative f, Monoid s) => Applicative (Components f s)
  where
    pure a = Components (bipure mempty (pure a))
    Components tsfg <*> Components tsfa =
      Components (bipure mappend (<*>) <<*>> tsfg <<*>> tsfa)

instance
  (Alternative f, Monoid s) => Alternative (Components f s)
  where
    empty = Components (bipure mempty empty)
    Components tsfa <|> Components tsfb =
      Components (bipure mappend (<|>) <<*>> tsfa <<*>> tsfb)

instance
  (Monoid (f a), Monoid s) => Monoid (Components f s a)
  where
    mempty = Components (bipure mempty mempty)
    mappend (Components tsfa) (Components tsfb) =
      Components (bipure mappend mappend <<*>> tsfa <<*>> tsfb)

data Pattern r a = Pattern (r a) a
  deriving (Functor, Foldable, Traversable)

hoistPattern
 :: (forall x . f x -> g x) -> Pattern f a -> Pattern g a
hoistPattern f (Pattern r a) = Pattern (f r) a

instance (Monoid (r a), Monoid a) => Monoid (Pattern r a) where
  mempty = Pattern mempty mempty
  Pattern r1 a1 `mappend` Pattern r2 a2 =
    Pattern (r1 `mappend` r2) (a1 `mappend` a2)

newtype Multi r a = Multi { getMulti :: r (NonEmpty a) }
  deriving (Functor, Foldable, Traversable)

instance Align r => Monoid (Multi r a) where
  mempty = Multi nil
  mappend (Multi a) (Multi b) =
    Multi (alignWith (these id id (<>)) a b)

newtype Abs r f m a = Abs (Block r f (Scope (Public ()) m) a)
  deriving (Functor, Foldable, Traversable)

hoistAbs
 :: (Functor r, Functor f, Functor m)
 => (forall x . m x -> n x)
 -> Abs r f m a -> Abs r f n a
hoistAbs f (Abs b) = Abs (hoistBlock (hoistScope f) b)

instance (Functor r, Functor f) => Bound (Abs r f) where
  Abs b >>>= f = Abs (b >>>= lift . f)

data Block r f m a =
    Defined (Pattern r (f (m a)))
  | Closure
      (Pattern r (f ()))
      (Scope (Local Int) m a)
      (Block r f (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

hoistBlock
 :: (Functor r, Functor f, Functor m)
 => (forall x . m x -> n x)
 -> Block r f m a
 -> Block r f n a
hoistBlock f (Defined r) = Defined (fmap f <$> r)
hoistBlock f (Closure p a b) =
  Closure p (hoistScope f a) (hoistBlock (hoistScope f) b)

instance (Functor r, Functor f) => Bound (Block r f) where
  Defined r     >>>= f = Defined (fmap (>>= f) <$> r)
  Closure p a b >>>= f = Closure p (a >>>= f) (b >>>= lift . f)

-- | Wrap nested expressions
class Monad m => MonadBlock r m | m -> r where
  wrapBlock :: r m a -> m a

  
{-
instance MonadBlock m => MonadBlock (Scope b m) where
  wrapBlock m = Scope (wrapBlock (hoistAbs unscope m))

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