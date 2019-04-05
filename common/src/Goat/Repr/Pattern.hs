--{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Goat.Repr.Pattern
  where

import Goat.Repr.Assoc
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
--import Data.Map (Map)
--import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Semigroup
import qualified Data.Monoid as Monoid (Alt(..))
import Data.Void (Void, absurd)
import Data.Functor.Identity (Identity(..))
--import Data.Functor.Alt
import Data.Functor.Plus (Alt(..), Plus(..))

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

iterPaths
 :: (a -> b)
 -> (forall x . r x -> (x -> These b c) -> c)
 -> Paths r a
 -> These b c
iterPaths = iterPaths' where
  iterPaths'
   :: (a -> b)
   -> (forall x . r x -> (x -> These b c) -> c)
   -> Paths r a
   -> These b c
  iterPaths' ka kf (Leaf a) = This (ka a)
  iterPaths' ka kf (Node r k) = That (iterNode ka kf r k)
  iterPaths' ka kf (Overlap r k a) =
    These (ka a) (iterNode ka kf r k)
  
  iterNode
   :: (a -> b)
   -> (forall x . r x -> (x -> These b c) -> c)
   -> r y
   -> (y -> Paths r a)
   -> c
  iterNode ka kf r k = kf r (iterPaths ka kf . k)

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
    In (f (m a))
  | Let p (m a) (Bindings f p (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

hoistBindings
 :: (Functor f, Functor m)
 => (forall x . m x -> n x)
 -> Bindings f p m a -> Bindings f p n a
hoistBindings f (In fm) = In (f <$> fm)
hoistBindings f (Let p m t) =
  Let p (f m) (hoistBindings (hoistScope f) t)

transBindings
 :: (forall x . f x -> g x)
 -> Bindings f p m a -> Bindings g p m a
transBindings f (In fm) = In (f fm)
transBindings f (Let p m t) = Let p m (transBindings f t)

liftBindings2
 :: (Functor f, Functor m)
 => (forall x . f x -> g x -> h x)
 -> Bindings f p m a -> Bindings g p m a -> Bindings h p m a
liftBindings2 f (In fm) (In gm) = In (f fm gm)
liftBindings2 f (Let p m tf) (In gm) =
  Let p m (liftBindings2 f tf (hoistBindings lift (In gm)))
liftBindings2 f tf (Let p m tg) =
  Let p m (liftBindings2 f (hoistBindings lift tf) tg)

embedBindings
 :: (Functor g, Monad m)
 => (forall x . f x -> Bindings g p m x)
 -> Bindings f p m a -> Bindings g p m a
embedBindings f (In fm) = f fm >>>= id
embedBindings f (Let p m t) =
  Let p m (embedBindings (hoistScope lift . f) t)
  
{-
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
-}

instance Functor f => Bound (Bindings f p) where
  In fma      >>>= f = In (fmap (>>= f) <$> fma)
  Let p ma ta >>>= f = Let p (ma >>= f) (ta >>>= lift . f)

instance (Alt f, Monad m) => Alt (Bindings f p m) where
  a <!> b = liftBindings2 (<!>) a b 

instance (Plus f, Monad m) => Plus (Bindings f p m) where
  zero = In zero

instance (Plus f, Monad m) => Monoid (Bindings f p m a) where
  mempty = zero
  mappend a b = a <!> b
  
newtype Multi r a = Multi { getMulti :: r (NonEmpty a) }
  deriving (Functor, Foldable, Traversable)

instance Align r => Alt (Multi r) where
  Multi a <!> Multi b =
    Multi (alignWith (these id id (<>)) a b)

instance Align r => Plus (Multi r) where
  zero = Multi nil
  
instance Align r => Monoid (Multi r a) where
  mempty = zero
  mappend = (<!>)
  
data Parts f g a = Parts (f a) (g a) deriving Functor

hoistParts
 :: (forall x . g x -> h x)
 -> Parts f g a -> Parts f h a
hoistParts f (Parts fa ga) = Parts fa (f ga)

instance (Align f, Align g) => Align (Parts f g) where
  nil = Parts nil nil
  alignWith f (Parts fa ga) (Parts fb gb) =
    Parts (alignWith f fa fb) (alignWith f ga gb)

instance (Alt f, Alt g) => Alt (Parts f g) where
  Parts fa ga <!> Parts fb gb = Parts (fa <!> ga) (fb <!> gb)

instance (Plus f, Plus g) => Plus (Parts f g) where
  zero = Parts zero zero

instance (Plus f, Plus g) => Monoid (Parts f g a) where
  mempty = zero
  mappend = (<!>)


patternDeclared
 :: ( Align f, Traversable t
    , Alternative g, Traversable g, Monoid s
    , MonadBlock (Abs Assoc (Components g s)) m
    )
 => Declared
      Assoc
      s
      (t (m Int ->
          Bindings
            (Multi f)
            (Decons (Components g s) Assoc ())
            m
            Int))
 -> (forall x. m x ->
      Bindings (Multi f) (Decons (Components g s) Assoc ()) m x)
 -> m b
 -> Bindings (Multi f) (Decons (Components g s) Assoc ()) m b
patternDeclared (Declared r k) f b =
  embedBindings
    (\ (Parts fm (Identity m)) -> Let fm <!> f (return m))
    (foldNode
      (\ (Tag s (Tag s' g, m)) -> (Tag (s `mappend` s') g, m))
      kv
      b)
  where
    Reveal kv = patternPaths . k <$> r
    

type Matchings f g m =
  ( g ()
  , Int ->
      Bindings (Parts f Maybe) (Decons g Assoc ()) m Int
  )

patternPaths
 :: ( Foldable t, Plus f
    , Alternative g, Traversable g
    , Monad m, MonadBlock (Abs Assoc g) m
    )
 => Paths Assoc (t (m Int -> Bindings f (Decons g Assoc ()) m Int))
 -> Matchings f g m
patternPaths =
  mergeMatchings
    . iterPaths
     -- (g (), a -> d m a)
      patternLeaf
     -- r b ->
     --   (b -> (g (), a -> d m a)) ->
     --   (g (), a -> d m a)
      patternNode
  where
    mergeMatchings
     :: (Alternative g, Plus f, Monad m)
     => These (Matchings f g m) (Matchings f g m)
     -> Matchings f g m
    mergeMatchings = these id id mergeMatchings'
      where
        mergeMatchings' (g1, t1) (g2, t2) =
          (g1 <|> g2, t1 `mappend` t2)
    
    patternNode
     :: ( Plus f, Alternative g, Traversable g
        , MonadBlock (Abs Assoc g) m
        )
     => Assoc x
     -> (x -> These (Matchings f g m) (Matchings f g m))
     -> Matchings f g m
    patternNode r k =
      ( pure ()
      , \ i ->
        foldNode (mergeMatchings . k <$> r) (return i)
      )
    
    patternLeaf
     :: (Foldable t, Alternative g, Plus f, Monad m)
     => t (m a -> Bindings f p m a)
     -> (g (), a -> Bindings (Parts f Maybe) p m a)
    patternLeaf t =
      (g, transBindings (\ f -> Parts f Nothing) . k . return)
      where
        (Monoid.Alt g, k) = foldMap pure t

foldNode
 :: ( Plus f, Alternative g, Traversable g
    , MonadBlock (Abs Assoc g) m, Applicative h
    )
 => Assoc (Matchings f g m)
 -> m a
 -> Bindings (Parts f h) (Decons g Assoc ()) m a
foldNode r a =
  embedBindings
    (\ p -> In (wrapRemaining p))
    (foldPattern
      (Pattern
        r
        (empty, \ a -> In (Parts zero (Just (return a)))))
      a)
  where
    wrapRemaining
     :: ( Functor f, Alternative g, Applicative h
        , MonadBlock (Abs Assoc g) m
        )
     => Parts f (Decons g Assoc) a -> Parts f h (m a)
    wrapRemaining (Parts f p) =
      Parts 
        (return <$> f)
        (pure (wrapBlock (Abs (Defined (return <$> p)))))

foldPattern
 :: (Plus f, Alternative g, Traversable g, Monad m)
 => Pattern Assoc (Matchings f g m)
 -> m a
 -> Bindings (Parts f (Decons g Assoc)) (Decons g Assoc ()) m a
foldPattern r a =
  Let pg a
    (hoistBindings lift
      (foldMapPattern' id rgm)
      >>>= Scope . return . B . Local)
  where
    pg = Decons (fst <$> r)
    -- (pg, rc) = sequenceBia rdg
    rgm =
      mapWithIndex (\ i (_, f) -> f i) r
      
    bind :: Monad m => Int -> Scope (Local Int) m a
    bind i = Scope (return (B (Local i)))
      
    foldMapPattern'
     :: (Plus f, Alternative g, Monad m)
     => (a -> Bindings (Parts f Maybe) (Decons g Assoc ()) m b)
     -> Pattern Assoc a
     -> Bindings
          (Parts f (Decons g Assoc))
          (Decons g Assoc ())
          m
          b
    foldMapPattern' f (Pattern ra a) =
      liftBindings2
        mergeParts
        (foldMapWithKey (\ n a -> hoistField n (f a)) ra)
        (hoistRemaining (f a))
      where
        mergeParts
         :: (Alt f, Functor r, Applicative g)
         => Parts f r a -> Parts f g a -> Parts f (Decons g r) a
        mergeParts (Parts f1 r) (Parts f2 g) =
          Parts (f1 <!> f2) (Decons (Pattern (pure <$> r) g))
        
        hoistField
         :: Ident
         -> Bindings (Parts f Maybe) (Decons g Assoc ()) m b
         -> Bindings (Parts f Assoc) (Decons g Assoc ()) m b
        hoistField n =
          transBindings (hoistParts (maybe mempty (singleton n)))
      
        hoistRemaining
         :: Alternative g
         => Bindings (Parts f Maybe) (Decons g Assoc ()) m b
         -> Bindings (Parts f g) (Decons g Assoc ()) m b
        hoistRemaining =
          transBindings
            (hoistParts (maybe empty pure))


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

newtype Decons f r a =
  Decons { getDecons :: Pattern r (f a) }
  deriving (Functor, Foldable, Traversable)

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
    Defined (Decons f r (m a))
  | Closure
      (Decons f r ())
      (Scope (Local Int) m a)
      (Block r f (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

hoistBlock
 :: (Functor r, Functor f, Functor m)
 => (forall x . m x -> n x)
 -> Block r f m a
 -> Block r f n a
hoistBlock f (Defined r) = Defined (f <$> r)
hoistBlock f (Closure p a b) =
  Closure p (hoistScope f a) (hoistBlock (hoistScope f) b)

instance (Functor r, Functor f) => Bound (Block r f) where
  Defined r     >>>= f = Defined ((>>= f) <$> r)
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