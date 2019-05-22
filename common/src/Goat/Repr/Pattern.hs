{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Goat.Repr.Pattern
  ( module Goat.Repr.Pattern
  , Bound(..), Alt(..), Plus(..)
  , Map(..), Text, Identity(..)
  ) where

import Goat.Util (swap, assoc, reassoc, (<&>))
import Bound
import Bound.Scope
import Control.Applicative (liftA2, Alternative(..))
import Control.Monad.Trans (lift)
import Control.Monad.Cont (cont, runCont)
import Data.These
import Data.Align
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Traversable (mapAccumL)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map 
import Data.Map (Map)
import Data.Text (Text)
import Data.Maybe (fromMaybe)
import Data.Semigroup ((<>))
--import qualified Data.Monoid as Monoid (Alt(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Plus (Alt(..), Plus(..))

{-
Pattern
----

The interpretation of pattern syntax is defined in
'Goat.Repr.Lang.Pattern'.
-}


-- |
bindRemaining
 :: (Alt f, Monad m)
 => (forall x. x -> Bindings f Decompose m x)
 -> Bindings (Parts f Identity) Decompose m a
 -> Bindings f Decompose m a
bindRemaining f =
  embedBindings
    (\ (Parts fm (Identity m)) ->
      Define (return <$> fm) <!> f m)

ignoreRemaining
 :: Monad m
 => Bindings (Parts f Identity) Decompose m a
 -> Bindings f Decompose m a
ignoreRemaining = transBindings (\ (Parts fm _) -> fm)

type BindMatchParts f g m =
  Int
   -> Bindings (Parts f Maybe) (Decompose NonEmpty g) m Int

bindPartsFromMatches
 :: ( Plus f, Applicative g
    , MonadBlock (Abs (Components NonEmpty g)) m
    , Applicative g', Applicative h
    )
 => Matches (Int -> Bindings f (Decompose NonEmpty h ()) m Int)
 -> a
 -> Bindings (Parts f g') (Decompose NonEmpty h ()) m a
bindPartsFromMatches (Matches r k) a =
  bindPartsFromNode
    (bindAssigns . fmap bindPartsFromLeaf . k <$> r)
    a
  where
    bindAssigns
     :: ( Plus f, Applicative g
        , MonadBlock (Abs (Components NonEmpty g)) m
        , Applicative h
        )
     => Assigns (Map Text) (NonEmpty (), BindMatchParts f h m)
     -> (NonEmpty (), BindMatchParts f h m)
    bindAssigns =
      merge .
      iterAssigns
        (bindPartsFromNode . fmap merge)
  
    merge
     :: Monoid m
     => These (NonEmpty (), m) m -> (NonEmpty (), m)
    merge (This p) = p
    merge (That m) = (pure (), m)
    merge (These (f, m) m') = (f <> pure (), m `mappend` m')
    
    
    bindPartsFromLeaf
     :: (Plus f, Functor p, Monad m)
     => NonEmpty (Int -> Bindings f p m Int)
     -> (NonEmpty (), Int -> Bindings (Parts f Maybe) p m Int)
    bindPartsFromLeaf (f:|fs) = (():|us, bindFirstPart)
      where
        (us, f') = foldMap pure fs
        bindFirstPart i =
          transBindings (`Parts` Nothing) (f i `mappend` f' i)

    bindPartsFromNode
      :: ( Plus f, Applicative g
         , MonadBlock (Abs (Components NonEmpty g)) m
         , Applicative g', Applicative h
         )
      => Map Text (NonEmpty (), BindMatchParts f h m)
      -> a
      -> Bindings (Parts f g') (Decompose NonEmpty h) m a
    bindPartsFromNode r a = letBind (Match p a) bs
      where
        (p, bs) = componentsMatchesFromNode r

componentsMatchesFromNode
 :: ( Plus f, Applicative g
    , MonadBlock (Abs (Components NonEmpty g)) m
    , Applicative g', Applicative h'
    )
 => Map Text (NonEmpty (), BindMatchParts f h m)
 -> ( Components NonEmpty h' ()
    , Bindings
        (Parts f g')
        (Decompose NonEmpty h (Scope (Local Int) m) b
    )
componentsMatchesFromNode r = (p, bs)
  where
    p = Components (Extend (fst <$> r) (pure ()))
    xm =
      bimapWithIndex
        (\ i (_, f) -> f i)
        (\ i g -> g i)
        (Extend r return)
    bs =
      hoistBindings lift (bindPartsFromExtension xm)
      >>>= \ i -> Scope (return (B (Local i)))
    
bindPartsFromExtension
 :: ( Plus f, Functor p, Applicative g
    , MonadBlock (Abs (Components NonEmpty g)) m
    , Applicative h
    )
 => Extend (Map Text) (Bindings (Parts f Maybe) p m a) (m a)
 -> Bindings (Parts f h) p m a
bindPartsFromExtension (Extend r m) =
  embedBindings
    wrapAndBindParts
    (liftBindings2 extendSecond brs (Define (pure m)))
  where
    brs =
      Map.foldMapWithKey
       (\ n -> transBindings (secondToField n))
       r
  
    extendSecond
      :: Alt f
      => Parts f (Inside g (Map Text)) a
      -> h a
      -> Parts f (Components g h) a
    extendSecond (Parts f (Inside r)) ha =
      Parts f (Components (Extend r ha))
    
    secondToField
     :: Text
     -> Parts f Maybe a
     -> Parts f (Inside NonEmpty (Map Text)) a
    secondToField n (Parts fa ma) =
      Parts fa (maybe mempty (Inside . Map.singleton n . pure) ma)
    
    wrapAndBindParts
     :: ( Functor f, Functor r
        , MonadBlock (Abs r) m
        , Applicative h
        )
     => Parts f r a -> Bindings (Parts f h) q m a
    wrapAndBindParts (Parts a b) =
      Define (Parts (return <$> a) b')
      where
        b' =
          pure (wrapBlock (Abs (Define (return <$> b))))

mapWithIndex
 :: Traversable t
 => (Int -> a -> b) -> t a -> t b
mapWithIndex f t =
  snd (mapAccumL (\ i a -> (i+1, f i a)) 0 t)

bimapWithIndex
 :: Bitraversable t
 => (Int -> a -> c) -> (Int -> b -> d) -> t a b -> t c d
bimapWithIndex f g t =
  snd 
    (bimapAccumL
      (\ i a -> (i+1, f i a))
      (\ i b -> (i+1, g i b))
      0
      t)

-- | Access control wrappers
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Foldable, Traversable, Monoid)

instance Applicative Public where
  pure = Public
  Public f <*> Public a = Public (f a)
  
newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable, Monoid)

instance Applicative Local where
  pure = Local
  Local f <*> Local a = Local (f a)

-- | Match data to selected parts of a value
data Matches a =
  forall x .
    Matches
      (Map Text x)
      (x -> Assigns (Map Text) (NonEmpty a))

sendMatches
 :: Map Text a -> Matches a
sendMatches r = Matches r (Leaf . pure)

wrapMatches
 :: Map Text (Assigns (Map Text) a) -> Matches a
wrapMatches r = Matches r (fmap pure)

instance Functor Matches where
  fmap f (Matches r k) =
    Matches r (fmap (fmap f) . k)

instance Foldable Matches where
  foldMap f (Matches r k) =
    foldMap (foldMap (foldMap f) . k) r

instance Traversable Matches where
  traverse f (Matches r k) =
    Matches <$> 
      traverse (traverse (traverse f) . k) r <*>
      pure id
      
instance Alt Matches where
  Matches ra ka <!> Matches rb kb =
    Matches
      (align ra rb)
      (fmap (these id id (<!>)) . bicrosswalkAssigns ka kb)

instance Plus Matches where
  zero = Matches mempty id
  
instance Monoid (Matches a) where
  mempty = zero
  mappend = (<!>)

-- | Declare assosiations between local and public paths and values
data Declares a =
  forall x .
    Declares
      (Local (Map Text x))
      (Public (Map Text x))
      (x -> Assigns (Map Text) (NonEmpty a))

wrapLocal
 :: Map Text (Assigns (Map Text) a) -> Declares a
wrapLocal kv = Declares (Local kv) mempty (fmap pure)

wrapPublic
 :: Map Text (Assigns (Map Text) a) -> Declares a
wrapPublic kv = Declares mempty (Public kv) (fmap pure)

instance Functor Declares where
  fmap f (Declares lr pr k) =
    Declares lr pr (fmap (fmap f) . k)

instance Foldable Declares where
  foldMap f (Declares lr pr k) =
    foldMap (foldMap (foldMap (foldMap f) . k)) lr
      `mappend`
        foldMap (foldMap (foldMap (foldMap f) . k)) pr

instance Traversable Declares where
  traverse f (Declares lr pr k) =
    Declares <$> 
      traverse (traverse (traverse (traverse f) . k)) lr <*>
      traverse (traverse (traverse (traverse f) . k)) pr <*>
      pure id
      
instance Alt Declares where
  Declares lra pra ka <!> Declares lrb prb kb =
    Declares
      (liftA2 align lra lrb)
      (liftA2 align pra prb)
      (fmap (these id id (<!>)) . bicrosswalkAssigns ka kb)

instance Plus Declares where
  zero = Declares mempty mempty id
  
instance Monoid (Declares a) where
  mempty = zero
  mappend = (<!>)


-- | Associate a set of fields with values, possibly ambiguously
data Assigns r a =
    forall x . Node (r x) (x -> Assigns r a)
  | Leaf a
  | forall x . Overlap (r x) (x -> Assigns r a) a

sendAssigns :: r a -> Assigns r a
sendAssigns r = Node r Leaf

wrapAssigns :: r (Assigns r a) -> Assigns r a
wrapAssigns r = Node r id

alignAssignsWith
 :: Align r
 => (These a b -> c)
 -> Assigns r a -> Assigns r b -> Assigns r c
alignAssignsWith = alignpw where
    alignnw
     :: Align r 
     => (These a b -> c)
     -> r x -> (x -> Assigns r a)
     -> r y -> (y -> Assigns r b)
     -> (forall xx . r xx -> (xx -> Assigns r c) -> p)
     -> p
    alignnw f ra ka rb kb g =
      g (align ra rb) (fmap f . bicrosswalkAssigns ka kb)
    
    alignpw
     :: Align r
     => (These a b -> c)
     -> Assigns r a -> Assigns r b -> Assigns r c
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

bicrosswalkAssigns
 :: Align r 
 => (a -> Assigns r c)
 -> (b -> Assigns r d)
 -> These a b
 -> Assigns r (These c d)
bicrosswalkAssigns f g (This a) = This <$> f a
bicrosswalkAssigns f g (That b) = That <$> g b
bicrosswalkAssigns f g (These a b) =
  alignAssignsWith id (f a) (g b)

iterAssigns
 :: Functor r
 => (r (These a b) -> b) -> Assigns r a -> These a b
iterAssigns = iter' where
  iter' _kf (Leaf a) = This a
  iter' kf (Node r k) = That (iterNode kf r k)
  iter' kf (Overlap r k a) = These a (iterNode kf r k)
  
  iterNode
   :: Functor r
   => (r (These a b) -> b) -> r x -> (x -> Assigns r a) -> b
  iterNode kf r k = kf (iterAssigns kf . k <$> r)

instance Functor (Assigns r) where
  fmap f (Node r k) = Node r (fmap f . k)
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Overlap r k a) = Overlap r (fmap f . k) (f a)

instance Foldable r => Foldable (Assigns r) where
  foldMap f (Node r k) = foldMap (foldMap f . k) r
  foldMap f (Leaf a) =  f a
  foldMap f (Overlap r k a) =
    foldMap (foldMap f . k) r `mappend` f a

instance Traversable r => Traversable (Assigns r) where
  traverse f = traverse' f where
    traverseNode
      :: (Traversable r, Applicative f)
      => (a -> f b)
      -> r x -> (x -> Assigns r a)
      -> (forall xx . r xx -> (xx -> Assigns r b) -> p)
      -> f p
    traverseNode f r k g =
      g <$> traverse (traverse f . k) r <*> pure id
    
    traverse' f (Node r k) =
      traverseNode f r k Node
    traverse' f (Leaf a) = Leaf <$> f a
    traverse' f (Overlap r k a) =
      traverseNode f r k Overlap <*> f a


-- | 'Bindings f p m a' binds expressions of type 'm a'
-- inside a container 'f' to patterns of type 'p'. 
data Bindings f p m a =
    Define (f (m a))
  | Let (Bindings (Parts p f) p (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

letBind
 :: (Functor f, Functor p, Monad m)
 => p a
 -> Bindings f p (Scope (Local Int) m) a
 -> Bindings f p m a
letBind pa bs =
  Let (liftBindings2 Parts (Define (return <$> pa)) bs)

transPattern
 :: (forall x . p x -> q x)
 -> Bindings f p m a -> Bindings f q m a
transPattern _f (Define fm) = Define fm
transPattern f (Let bs) =
  Let (transBindings (first' f) (transPattern f bs))
  where
    first' :: (f a -> f' a) -> Parts f g a -> Parts f' g a
    first' f (Parts fa ga) = Parts (f fa) ga

-- | Higher order map over expression type.
hoistBindings
 :: (Functor f, Functor p, Functor m)
 => (forall x . m x -> n x)
 -> Bindings f p m a -> Bindings f p n a
hoistBindings f (Define fm) = Define (f <$> fm)
hoistBindings f (Let t) = Let (hoistBindings (hoistScope f) t)

-- | Higher order map over container type.
transBindings
 :: (forall x . f x -> g x)
 -> Bindings f p m a -> Bindings g p m a
transBindings f (Define fm) = Define (f fm)
transBindings f (Let t) =
  Let (transBindings (second' f) t)
  where
    second' :: (g a -> g' a) -> Parts f g a -> Parts f g' a
    second' f (Parts fa ga) = Parts fa (f ga)

-- | Higher order traverse over container type.
transverseBindings
 :: Functor h
 => (forall x . f x -> h (g x))
 -> Bindings f p m a -> h (Bindings g p m a)
transverseBindings f (Define fm) = Define <$> f fm
transverseBindings f (Let t) =
  Let <$> transverseBindings (second' f) t
  where
    second'
     :: Functor h
     => (g a -> h (g' a)) -> Parts f g a -> h (Parts f g' a)
    second' f (Parts fa ga) = Parts fa <$> f ga

-- | Higher order applicative function lifting over container type.
liftBindings2
 :: (Functor f, Functor g, Functor p, Monad m)
 => (forall x . f x -> g x -> h x)
 -> Bindings f p m a -> Bindings g p m a -> Bindings h p m a
liftBindings2 f (Define fm) (Define gm) = Define (f fm gm)
liftBindings2 f (Let tf) (Define gm) =
  Let
    (liftBindings2 (first' f)
      tf
      (hoistBindings lift (Define gm)))
  where
    first'
     :: (f a -> g a -> h a)
     -> Parts p f a -> g a -> Parts p h a
    first' f (Parts pa fa) ga = Parts pa (f fa ga)
liftBindings2 f tf (Let tg) =
  Let
    (liftBindings2 (second' f)
      (hoistBindings lift tf)
      tg)
  where
    second'
     :: (f a -> g a -> h a) 
     -> f a -> Parts p g a -> Parts p h a
    second' f fa (Parts pa ga) = Parts pa (f fa ga)

-- | Higher order bind over container type.
embedBindings
 :: (Functor g, Functor p, Monad m)
 => (forall x . f x -> Bindings g p m x)
 -> Bindings f p m a -> Bindings g p m a
embedBindings f (Define fm) = f fm >>>= id
embedBindings f (Let t) =
  Let (embedBindings (hoistBindings lift . second' f) t)
  where
    second'
     :: (Functor g, Functor p, Monad m)
     => (f a -> Bindings g p m a)
     -> Parts p f a -> Bindings (Parts p g) p m a
    second' f (Parts pa fa) =
      liftBindings2 Parts (Define (return <$> pa)) (f fa)

-- | Higher order join over container type
squashBindings
 :: (Functor f, Functor p, Monad m)
 => Bindings (Bindings f p m) p m a -> Bindings f p m a
squashBindings = embedBindings id

instance (Functor f, Functor p) => Bound (Bindings f p) where
  Define fm >>>= f = Define ((>>= f) <$> fm)
  Let t   >>>= f = Let (t >>>= lift . f)

instance
  (Alt f, Functor p, Monad m) => Alt (Bindings f p m)
  where
    a <!> b = liftBindings2 (<!>) a b 

instance
  (Plus f, Functor p, Monad m) => Plus (Bindings f p m)
  where
    zero = Define zero

instance
  (Plus f, Functor p, Monad m) => Monoid (Bindings f p m a)
  where
    mempty = zero
    mappend a b = a <!> b

  
-- 
type Decompose f g = Match (Components f g ())

newtype Components f g a =
  Components (Extend (Map Text) (f a) (g a))

instance (Functor f, Functor g) => Functor (Components f g) where
  fmap f (Components x) = Components (bimap (fmap f) (fmap f) x)

instance
  (Foldable f, Foldable g) => Foldable (Components f g)
  where
  foldMap f (Components x) = bifoldMap (foldMap f) (foldMap f) x

instance
  (Traversable f, Traversable g) => Traversable (Components f g)
  where
  traverse f (Components x) =
    Components <$> bitraverse (traverse f) (traverse f) x
    
-- | Match a value 'a' against pattern 'p'
data Match p a = Match p a
  deriving (Functor, Foldable, Traversable)

instance Bifunctor Match where
  bimap f g (Match p a) = Match (f p) (g a)

-- Combine an additional 'leftover' value to a container 'r'.
data Extend r a b = Extend (r a) b
  deriving (Functor, Foldable, Traversable)

instance Functor r => Bifunctor (Extend r) where
  bimap f g (Extend r b) = Extend (f <$> r) (g b)

instance Foldable r => Bifoldable (Extend r) where
  bifoldMap f g (Extend r b) = foldMap f r `mappend` g b

instance Traversable r => Bitraversable (Extend r) where
  bitraverse f g (Extend r b) =
    Extend <$> traverse f r <*> g b

instance (Monoid (r a), Monoid b) => Monoid (Extend r a b) where
  mempty = Extend mempty mempty
  Extend r1 b1 `mappend` Extend r2 b2 =
    Extend (r1 `mappend` r2) (b1 `mappend` b2)

-- A lifted compose type like 'Data.Functor.Compose'
-- with some different instances

newtype Inside f r a = Inside { getInside :: r (f a) }
  deriving (Functor, Foldable, Traversable)
  
instance (Alt f, Align r) => Alt (Inside f r) where
  Inside a <!> Inside b =
    Inside (alignWith (these id id (<!>)) a b)

instance (Alt f, Align r) => Plus (Inside f r) where
  zero = Inside nil
  
instance (Alt f, Align r) => Monoid (Inside f r a) where
  mempty = zero
  mappend = (<!>)

-- A lifted product like 'Data.Functor.Product'
-- with some different instances

data Parts f g a = Parts (f a) (g a)
  deriving (Functor, Foldable, Traversable)

instance (Align f, Align g) => Align (Parts f g) where
  nil = Parts nil nil
  alignWith f (Parts fa ga) (Parts fb gb) =
    Parts (alignWith f fa fb) (alignWith f ga gb)

instance (Alt f, Alt g) => Alt (Parts f g) where
  Parts fa ga <!> Parts fb gb = Parts (fa <!> fb) (ga <!> gb)

instance (Plus f, Plus g) => Plus (Parts f g) where
  zero = Parts zero zero

instance
  (Monoid (f a), Monoid (g a)) => Monoid (Parts f g a)
  where
    mempty = Parts mempty mempty
    Parts fa ga `mappend` Parts fb gb =
      Parts (fa `mappend` fb) (ga `mappend` gb)

-- |
type Ident = Text

newtype Block f p m a = 
  Block (Bindings f p (Scope (Public Ident) m) a)

-- | Wrap nested expressions
class Monad m => MonadBlock r m | m -> r where
  wrapBlock :: r m a -> m a
