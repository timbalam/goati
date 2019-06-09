{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances, FlexibleContexts, ScopedTypeVariables, LambdaCase #-}
{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Goat.Repr.Pattern
  ( module Goat.Repr.Pattern
  , Map, Text, Scope(..), Var(..)
  )
where

import Goat.Util (swap, assoc, reassoc, (<&>))
import Bound
import Bound.Scope
import Control.Applicative (liftA2, Alternative(..))
import Control.Monad.Trans (lift)
import Control.Monad.State (evalState, state)
import Data.These
import Data.Align
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Bifunctor.Join (Join(..))
-- import Data.Traversable (mapAccumL)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map 
import Data.Map (Map)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Maybe (fromMaybe)
import Data.Semigroup ((<>))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Plus (Alt(..), Plus(..))
import Prelude.Extras (Eq1(..), Show1(..), Lift1(..))

{-
Pattern
----

The interpretation of pattern syntax is defined in
'Goat.Repr.Lang.Pattern'.
-}


-- |
bindRemaining
 :: (Alt f, Functor p, Monad m)
 => (forall x. x -> Bindings f p m x)
 -> Bindings (Parts f Identity) p m a
 -> Bindings f p m a
bindRemaining f
  = embedBindings
      (\ (Parts fm (Identity m))
       -> Define (return <$> fm) <!> f m)

ignoreRemaining
 :: Monad m
 => Bindings (Parts f Identity) p m a
 -> Bindings f p m a
ignoreRemaining
  = transBindings (\ (Parts fm _) -> fm)

type Split f = Parts f Maybe
type AmbigCpts = Inside NonEmpty (Map Text)
type BlockCpts = Block AmbigCpts

bindPartsFromMatches
 :: ( Plus f, Applicative g
    , MonadBlock BlockCpts m
    )
 => Matches
      (Int -> Bindings f AmbigCpts m Int)
 -> a -> Bindings (Parts f g) AmbigCpts m a
bindPartsFromMatches (Matches r k) a
  = bindPartsFromNode
      (bindAssigns
        . fmap bindPartsFromLeaf
        . k
       <$> r)
      a
  where
  bindAssigns
   :: (Plus f, MonadBlock BlockCpts m)
   => Assigns (Map Text)
        ( Int
           -> Bindings (Split f) AmbigCpts m Int
        , NonEmpty ()
        )
   -> ( Int
         -> Bindings (Split f) AmbigCpts m Int
      , NonEmpty ()
      )
  bindAssigns
    = merge
    . iterAssigns
        (bindPartsFromNode . fmap merge)
  
  merge
   :: Monoid m
   => These (m, NonEmpty ()) m
   -> (m, NonEmpty ())
  merge
    = \case
      This p
       -> p
      
      That m
       -> (m, pure ())
      
      These (m, f) m'
       -> (m `mappend` m', f <!> pure ())
  
  bindPartsFromLeaf
   :: (Plus f, Functor p, Monad m)
   => NonEmpty (Int -> Bindings f p m Int)
   -> ( Int -> Bindings (Parts f Maybe) p m Int
      , NonEmpty ()
      )
  bindPartsFromLeaf fs
    = (bindFirstPart, us)
    where
    (f', us) = traverse (\ f -> (f, ())) fs
    bindFirstPart i
      = transBindings (`Parts` Nothing) (f' i)

  bindPartsFromNode
   :: (Plus f, Applicative g, MonadBlock BlockCpts m)
   => Map Text
        ( Int -> Bindings (Split f) AmbigCpts m Int
        , NonEmpty ()
        )
   -> a -> Bindings (Parts f g) AmbigCpts m a
  bindPartsFromNode r a
    = Match p (return a) bs
    where
    (p, bs) = componentsMatchesFromNode r

componentsMatchesFromNode
 :: ( Plus f, Applicative g, Functor p
    , MonadBlock BlockCpts m
    )
 => Map Text
      ( Int -> Bindings (Split f) p m Int
      , NonEmpty ()
      )
 -> ( AmbigCpts ()
    , Bindings (Parts f g) p (Scope (Local Int) m) b
    )
componentsMatchesFromNode r
  = (p, bs)
  where
  p = Inside (snd <$> r)
  xm
    = bimapWithIndex
        (\ i (f, _) -> f i)
        (\ i g -> g i)
        (Extend r return)
  bs
    = hoistBindings lift (bindPartsFromExtension xm)
   >>>= \ i -> Scope (return (B (Local i)))
    
bindPartsFromExtension
 :: ( Plus f, Applicative g, Functor p
    , MonadBlock BlockCpts m
    )
 => Extend (Map Text)
      (Bindings (Split f) p m a) (m a)
 -> Bindings (Parts f g) p m a
bindPartsFromExtension (Extend r m)
  = embedBindings
      bindParts
      (liftBindings2 wrapSecond
        brs
        (Define (pure m)))
  where
  brs
    = Map.foldMapWithKey
        (\ n -> transBindings (secondToField n))
        r
  
  wrapSecond
    :: ( Functor g, Applicative h
       , MonadBlock (Block (Inside h g)) m
       )
    => Parts f g a
    -> Identity a
    -> Parts f m a
  wrapSecond (Parts fa ga) (Identity a)
    = Parts fa
        (wrapBlock
          (Block
            (Extend
              (Inside (pure . return <$> ga))
              (pure (return a)))))
    
  secondToField
   :: Text
   -> Parts f Maybe a
   -> Parts f (Map Text) a
  secondToField n (Parts fa ma)
    = Parts fa
        (maybe Map.empty (Map.singleton n) ma)
  
  bindParts
   :: (Functor f, Applicative h, Monad m)
   => Parts f m a -> Bindings (Parts f h) q m a
  bindParts (Parts a b)
    = Define (Parts (return <$> a) (pure b))

mapWithIndex
 :: Traversable t
 => (Int -> a -> b) -> t a -> t b
mapWithIndex f t
  = evalState
      (traverse
        (\ a -> state (\ i -> (f i a, i+1)))
        t)
      0

bimapWithIndex
 :: Bitraversable t
 => (Int -> a -> c) -> (Int -> b -> d) -> t a b -> t c d
bimapWithIndex f g t
  = evalState
      (bitraverse
        (\ a -> state (\ i -> (f i a, i+1)))
        (\ b -> state (\ i -> (g i b, i+1)))
        t)
      0

-- | Access control wrappers
newtype Public a = Public a
  deriving
    ( Eq, Show
    , Functor, Foldable, Traversable, Monoid
    )

instance Applicative Public where
  pure = Public
  Public f <*> Public a = Public (f a)
  
newtype Local a = Local a
  deriving
    ( Eq, Show
    , Functor, Foldable, Traversable, Monoid
    )

instance Applicative Local where
  pure = Local
  Local f <*> Local a = Local (f a)

newtype Super a = Super a deriving (Eq, Show)

-- | Match data to selected parts of a value
data Matches a
  = forall x
  . Matches
      (Map Text x)
      (x -> Assigns (Map Text) (NonEmpty a))

sendMatches
 :: Map Text a -> Matches a
sendMatches r = Matches r (Leaf . pure)

wrapMatches
 :: Map Text (Assigns (Map Text) a) -> Matches a
wrapMatches r = Matches r (fmap pure)

instance Functor Matches where
  fmap f (Matches r k)
    = Matches r (fmap (fmap f) . k)

instance Foldable Matches where
  foldMap f (Matches r k)
    = foldMap (foldMap (foldMap f) . k) r

instance Traversable Matches where
  traverse f (Matches r k)
    = Matches
   <$> traverse (traverse (traverse f) . k) r
   <*> pure id
      
instance Alt Matches where
  Matches ra ka <!> Matches rb kb
    = Matches
        (align ra rb)
        (fmap (these id id (<!>))
          . bicrosswalkAssigns ka kb)

instance Plus Matches where
  zero = Matches mempty id
  
instance Monoid (Matches a) where
  mempty = zero
  mappend = (<!>)

-- | Declare assosiations between local and public paths and values
data Declares a
  = forall x
  . Declares
      (Local (Map Text x))
      (Public (Map Text x))
      (x -> Assigns (Map Text) (NonEmpty a))

wrapLocal
 :: Map Text (Assigns (Map Text) a) -> Declares a
wrapLocal kv = Declares (Local kv) mempty (fmap pure)

wrapPublic
 :: Map Text (Assigns (Map Text) a) -> Declares a
wrapPublic kv
  = Declares mempty (Public kv) (fmap pure)

instance Functor Declares where
  fmap f (Declares lr pr k)
    = Declares lr pr (fmap (fmap f) . k)

instance Foldable Declares where
  foldMap f (Declares lr pr k)
    = foldMap
        (foldMap (foldMap (foldMap f) . k)) lr
    `mappend`
      foldMap
        (foldMap (foldMap (foldMap f) . k)) pr

instance Traversable Declares where
  traverse f (Declares lr pr k)
    = Declares
   <$> traverse
        (traverse (traverse (traverse f) . k))
        lr
   <*> traverse
        (traverse (traverse (traverse f) . k))
        pr
   <*> pure id
      
instance Alt Declares where
  Declares lra pra ka <!> Declares lrb prb kb
    = Declares
        (liftA2 align lra lrb)
        (liftA2 align pra prb)
        (fmap (these id id (<!>))
          . bicrosswalkAssigns ka kb)

instance Plus Declares where
  zero = Declares mempty mempty id
  
instance Monoid (Declares a) where
  mempty = zero
  mappend = (<!>)


-- | Associate a set of fields with values, possibly ambiguously
data Assigns r a
  = forall x
  . Node (r x) (x -> Assigns r a)
  | Leaf a
  | forall x
  . Overlap (r x) (x -> Assigns r a) a

sendAssigns :: r a -> Assigns r a
sendAssigns r = Node r Leaf

wrapAssigns :: r (Assigns r a) -> Assigns r a
wrapAssigns r = Node r id

alignAssignsWith
 :: Align r
 => (These a b -> c)
 -> Assigns r a -> Assigns r b -> Assigns r c
alignAssignsWith
  = alignpw
  where
  alignnw
   :: Align r 
   => (These a b -> c)
   -> r x -> (x -> Assigns r a)
   -> r y -> (y -> Assigns r b)
   -> (forall xx
        . r xx
       -> (xx -> Assigns r c)
       -> p)
   -> p
  alignnw f ra ka rb kb g
    = g (align ra rb)
        (fmap f . bicrosswalkAssigns ka kb)
  
  alignpw
   :: Align r
   => (These a b -> c)
   -> Assigns r a
   -> Assigns r b
   -> Assigns r c
  alignpw f (Node ra ka) (Node rb kb)
    = alignnw f ra ka rb kb Node
  alignpw f (Node ra ka) (Leaf b)
    = Overlap ra (fmap (f . This) . ka) (f (That b))
  alignpw f (Node ra ka) (Overlap rb kb b)
    = alignnw f ra ka rb kb Overlap (f (That b))
  alignpw f (Leaf a) (Node rb kb)
    = Overlap rb (fmap (f . That) . kb) (f (This a))
  alignpw f (Leaf a) (Leaf b)
    = Leaf (f (These a b))
  alignpw f (Leaf a) (Overlap rb kb b)
    = Overlap rb
        (fmap (f . That) . kb)
        (f (These a b))
  alignpw f (Overlap ra ka a) (Node rb kb)
    = alignnw f ra ka rb kb Overlap (f (This a))
  alignpw f (Overlap ra ka a) (Leaf b)
    = Overlap ra
        (fmap (f . This) . ka)
        (f (These a b))
  alignpw f (Overlap ra ka a) (Overlap rb kb b)
    = alignnw f ra ka rb kb Overlap (f (These a b))

bicrosswalkAssigns
 :: Align r 
 => (a -> Assigns r c)
 -> (b -> Assigns r d)
 -> These a b
 -> Assigns r (These c d)
bicrosswalkAssigns f g
  = \case
    This a -> This <$> f a
    That b -> That <$> g b
    These a b -> alignAssignsWith id (f a) (g b)

iterAssigns
 :: Functor r
 => (r (These a b) -> b)
 -> Assigns r a
 -> These a b
iterAssigns
  = iter'
  where
  iter' _kf (Leaf a)
    = This a
  iter' kf (Node r k)
    = That (iterNode kf r k)
  iter' kf (Overlap r k a)
    = These a (iterNode kf r k)
  
  iterNode
   :: Functor r
   => (r (These a b) -> b)
   -> r x
   -> (x -> Assigns r a)
   -> b
  iterNode kf r k = kf (iterAssigns kf . k <$> r)

instance Functor (Assigns r) where
  fmap f (Node r k)
    = Node r (fmap f . k)
  fmap f (Leaf a)
    = Leaf (f a)
  fmap f (Overlap r k a)
    = Overlap r (fmap f . k) (f a)

instance Foldable r => Foldable (Assigns r) where
  foldMap f (Node r k)
    = foldMap (foldMap f . k) r
  foldMap f (Leaf a)
    = f a
  foldMap f (Overlap r k a)
    = foldMap (foldMap f . k) r `mappend` f a

instance
  Traversable r => Traversable (Assigns r)
  where
  traverse
    = traverse'
    where
    traverseNode
     :: (Traversable r, Applicative f)
     => (a -> f b)
     -> r x -> (x -> Assigns r a)
     -> (forall xx
          . r xx
         -> (xx -> Assigns r b)
         -> p)
     -> f p
    traverseNode f r k g
      = g
     <$> traverse (traverse f . k) r
     <*> pure id
    
    traverse' f (Node r k)
      = traverseNode f r k Node
    traverse' f (Leaf a)
      = Leaf <$> f a
    traverse' f (Overlap r k a)
      = traverseNode f r k Overlap <*> f a


-- | 'Bindings f p m a' binds expressions of type 'm a'
-- inside a container 'f' to patterns of type 'p'. 
data Bindings f p m a
  = Define (f (m a))
  | Match (p ()) (m a)
      (Bindings f p (Scope (Local Int) m) a)
  | Index
      (Bindings (Parts p f) p
        (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

instance
  ( Functor f, Eq1 f
  , Functor p, Eq1 p
  , Monad m, Eq1 m
  )
   => Eq1 (Bindings f p m)
  where
  Define fma ==# Define fmb
    = (Lift1 <$> fma) ==# (Lift1 <$> fmb)
  Match pa ma bsa ==# Match pb mb bsb
    = pa ==# pb && ma ==# mb && bsa ==# bsb
  Index bsa ==# Index bsb
    = bsa ==# bsb

instance
  ( Functor f, Eq1 f
  , Functor p, Eq1 p
  , Monad m, Eq1 m
  , Eq a
  )
   => Eq (Bindings f p m a)
  where
  (==) = (==#)

instance
  ( Functor f, Show1 f
  , Functor p, Show1 p
  , Functor m, Show1 m
  )
   => Show1 (Bindings f p m)
  where
  showsPrec1 d
    = \case
      Define fma
       -> showParen (d>10)
            (showString "Define " 
              . showsPrec1 11 (Lift1 <$> fma))
      
      Match p ma bs
       -> showParen (d>10)
            (showString "Match "
              . showsPrec1 11 p
              . showChar ' '
              . showsPrec1 11 ma
              . showChar ' '
              . showsPrec1 11 bs)
      
      Index bs
       -> showParen (d>10)
            (showString "Index "
              . showsPrec1 11 bs)

instance
  ( Functor f, Show1 f
  , Functor p, Show1 p
  , Functor m, Show1 m, Show a)
   => Show (Bindings f p m a)
  where
  showsPrec = showsPrec1

substituteBindings
 :: forall f p m a
  . (Functor f, Functor p, Foldable p, Monad m)
 => (p () -> m a -> [m a])
 -> Bindings f p m a -> f (m a)
substituteBindings k
  = \case
    Define fm
     -> fm
    
    Match p m bs
     -> instantiateBindings (k p m) bs
    
    Index bs
     -> let
        Parts pv fv
          = instantiateBindings (foldMap pure pv) bs
        in fv
  
  where
  instantiateBindings vs bs
    = subst <$> substituteBindings k' bs
    where
    k' p s = map lift (k p (subst s))
    subst = instantiate get
    get (Local i) = vs !! i
    

-- | Higher order map over expression type.
hoistBindings
 :: (Functor f, Functor p, Functor m)
 => (forall x . m x -> n x)
 -> Bindings f p m a -> Bindings f p n a
hoistBindings f
  = \case 
    Define fm
     -> Define (f <$> fm)
    
    Match p m bs
     -> Match p (f m)
          (hoistBindings (hoistScope f) bs)
    
    Index bs
     -> Index (hoistBindings (hoistScope f) bs)

-- | Higher order map over container type.
transBindings
 :: (forall x . f x -> g x)
 -> Bindings f p m a -> Bindings g p m a
transBindings f
  = \case
    Define fm -> Define (f fm)
    Match p m bs -> Match p m (transBindings f bs)
    Index bs -> Index (transBindings (second' f) bs)
  where
  second'
   :: (f a -> g a) -> Parts p f a -> Parts p g a
  second' f (Parts pa fa) = Parts pa (f fa)

transPattern
 :: (forall x . p x -> q x)
 -> Bindings f p m a -> Bindings f q m a
transPattern f
  = \case 
    Define fm
     -> Define fm
    
    Match p m bs
     -> Match (f p) m (transPattern f bs)
    
    Index bs
     -> Index
          (transBindings (first' f)
            (transPattern f bs))
  where
  first'
   :: (p a -> q a) -> Parts p f a -> Parts q f a
  first' f (Parts pa fa) = Parts (f pa) fa

-- | Higher order traverse over container type.
transverseBindings
 :: Functor h
 => (forall x . f x -> h (g x))
 -> Bindings f p m a -> h (Bindings g p m a)
transverseBindings f
  = \case
    Define fm
     -> Define <$> f fm
    
    Match p m bs
     -> Match p m <$> transverseBindings f bs
    
    Index bs
     -> Index <$> transverseBindings (second' f) bs
  where
  second'
   :: Functor h
   => (f a -> h (g a))
   -> Parts p f a -> h (Parts p g a)
  second' f (Parts pa fa) = Parts pa <$> f fa

bitransverseBindings
 :: Applicative h
 => (forall x x' . (x -> h x') -> f x -> h (g x'))
 -> (forall x x' . (x -> h x') -> p x -> h (q x'))
 -> (forall x x' . (x -> h x') -> m x -> h (n x'))
 -> (a -> h b)
 -> Bindings f p m a -> h (Bindings g q n b)
bitransverseBindings f g h i
  = \case
    Define fm
     -> Define <$> f (h i) fm
    
    Match p m bs
     -> Match
     <$> g pure p
     <*> h i m
     <*> bitransverseBindings
          f g (bitransverseScope h) i bs
    
    Index bs
     -> Index
     <$> bitransverseBindings
          (both' g f) g (bitransverseScope h) i bs
  
  where
  both'
   :: Applicative h
   => (forall x x' . (x -> h x') -> p x -> h (q x'))
   -> (forall x x' . (x -> h x') -> f x -> h (g x'))
   -> (a -> h b) -> Parts p f a -> h (Parts q g b)
  both' f g h (Parts pa fa)
    = Parts <$> f h pa <*> g h fa

-- | Higher order applicative function lifting over container type.
liftBindings2
 :: (Functor f, Functor g, Functor p, Monad m)
 => (forall x . f x -> g x -> h x)
 -> Bindings f p m a
 -> Bindings g p m a
 -> Bindings h p m a
liftBindings2 f (Define fm) (Define gm)
  = Define (f fm gm)
liftBindings2 f (Match p m bsf) (Define gm)
  = Match p m 
      (liftBindings2 f
        bsf
        (hoistBindings lift (Define gm)))
liftBindings2 f (Index bsf) (Define gm)
  = Index
      (liftBindings2 (first' f)
        bsf
        (hoistBindings lift (Define gm)))
  where
  first'
   :: (f a -> g a -> h a)
   -> Parts p f a -> g a -> Parts p h a
  first' f (Parts pa fa) ga = Parts pa (f fa ga)
liftBindings2 f bsf (Match p m bsg)
  = Match p m
      (liftBindings2 f (hoistBindings lift bsf) bsg)
liftBindings2 f bsf (Index bsg)
  = Index
      (liftBindings2 (second' f)
        (hoistBindings lift bsf)
        bsg)
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
embedBindings f (Define fm)
  = f fm >>>= id
embedBindings f (Match p m bs)
  = Match p m
      (embedBindings (hoistBindings lift . f) bs)
embedBindings f (Index bs)
  = Index
      (embedBindings
        (hoistBindings lift . second' f) bs)
  where
  second'
   :: (Functor g, Functor p, Monad m)
   => (f a -> Bindings g p m a)
   -> Parts p f a -> Bindings (Parts p g) p m a
  second' f (Parts pa fa)
    = liftBindings2 Parts
        (Define (return <$> pa))
        (f fa)

-- | Higher order join over container type
squashBindings
 :: (Functor f, Functor p, Monad m)
 => Bindings (Bindings f p m) p m a
 -> Bindings f p m a
squashBindings = embedBindings id

instance
  (Functor f, Functor p) => Bound (Bindings f p) 
  where
  Define fm >>>= f
    = Define ((>>= f) <$> fm)
    
  Match p m bs >>>= f
    = Match p (m >>= f) (bs >>>= lift . f)
    
  Index bs >>>= f
    = Index (bs >>>= lift . f)

instance
  (Alt f, Functor p, Monad m) => Alt (Bindings f p m)
  where a <!> b = liftBindings2 (<!>) a b 

instance
  (Plus f, Functor p, Monad m)
   => Plus (Bindings f p m)
  where zero = Define zero

instance
  (Plus f, Functor p, Monad m)
    => Monoid (Bindings f p m a)
  where
  mempty = zero
  mappend a b = a <!> b

-- Combine an additional 'leftover' value to a container 'r'.
data Extend r a b = Extend (r a) b
  deriving (Functor, Foldable, Traversable, Eq, Show)

instance Functor r => Bifunctor (Extend r) where
  bimap f g (Extend r b) = Extend (f <$> r) (g b)

instance Foldable r => Bifoldable (Extend r) where
  bifoldMap f g (Extend r b)
    = foldMap f r `mappend` g b

instance
  Traversable r => Bitraversable (Extend r)
  where
  bitraverse f g (Extend r b)
    = Extend <$> traverse f r <*> g b

instance
  (Monoid (r a), Monoid b) => Monoid (Extend r a b) 
  where
  mempty
    = Extend mempty mempty
  
  Extend r1 b1 `mappend` Extend r2 b2
    = Extend (r1 `mappend` r2) (b1 `mappend` b2)

-- A lifted compose type like 'Data.Functor.Compose'
-- with some different instances

newtype Inside f r a
  = Inside { getInside :: r (f a) }
  deriving (Functor, Foldable, Traversable)

instance 
  (Applicative f, Applicative r)
   => Applicative (Inside f r)
  where
  pure a = Inside (pure (pure a))
  Inside rff <*> Inside rfa
    = Inside ((<*>) <$> rff <*> rfa)

instance (Alt f, Align r) => Alt (Inside f r) where
  Inside a <!> Inside b
    = Inside (alignWith (these id id (<!>)) a b)

instance (Alt f, Align r) => Plus (Inside f r) where
  zero = Inside nil

instance
  (Alt f, Align r) => Monoid (Inside f r a)
  where
  mempty = zero
  mappend = (<!>)

-- A lifted product like 'Data.Functor.Product'
-- with some different instances

data Parts f g a = Parts (f a) (g a)
  deriving (Functor, Foldable, Traversable)

instance (Eq1 f, Eq1 g) => Eq1 (Parts f g) where
  Parts fa ga ==# Parts fb gb
    = fa ==# fb && ga ==# gb

instance
  (Eq1 f, Eq1 g, Eq a) => Eq (Parts f g a)
  where
  (==) = (==#)

instance
  (Show1 f, Show1 g) => Show1 (Parts f g)
  where
  showsPrec1 d (Parts fa ga)
    = showParen (d>10)
        (showString "Parts "
          . showsPrec1 11 fa
          . showChar ' '
          . showsPrec1 11 ga)

instance
  (Show1 f, Show1 g, Show a) => Show (Parts f g a)
  where
  showsPrec = showsPrec1

instance
  (Align f, Align g) => Align (Parts f g)
  where
  nil = Parts nil nil
  alignWith f (Parts fa ga) (Parts fb gb)
    = Parts (alignWith f fa fb) (alignWith f ga gb)

instance (Alt f, Alt g) => Alt (Parts f g) where
  Parts fa ga <!> Parts fb gb
    = Parts (fa <!> fb) (ga <!> gb)

instance (Plus f, Plus g) => Plus (Parts f g) where
  zero = Parts zero zero

instance
  (Monoid (f a), Monoid (g a))
    => Monoid (Parts f g a)
  where
  mempty = Parts mempty mempty
  Parts fa ga `mappend` Parts fb gb
    = Parts (fa `mappend` fb) (ga `mappend` gb)

-- |
type Ident = Text

showIdent :: Ident -> String
showIdent = Text.unpack

newtype Block f m a
  = Block
      (Extend f
        (Scope (Super Ident)
          (Scope (Public Ident) m) a)
        (Maybe (m a)))
{-
hoistAbs
 :: (Functor f, Functor p, Functor m)
 => (forall x . m x -> n x)
 -> Abs f p m a -> Abs f p n a
hoistAbs f (Ext bs m)
  = Ext
      (hoistBindings (hoistScope f) bs)
      (f m)

instance
  (Functor f, Functor p, Functor m)
   => Functor (Abs f p m)
  where
  f <$> Ext bs m = Ext (f <$> bs) (f <$> x)

instance
  (Foldable f, Foldable p, Foldable m)
   => Foldable (Abs f p m)
  where
  foldMap f (Ext bs m)
    = foldMap f bs `mappend` foldMap f m

instance
  (Traversable f, Traversable p, Traversable m)
   => Traversable (Abs f p m)
  where
  traverse f (Ext bs m)
    = Ext
   <$> traverse f bs
   <*> traverse f m

instance
  (Functor f, Functor p) => Bound (Abs f p)
  where
  Ext bs m >>>= f = Ext (bs >>>= lift . f) (m >>= f)
-}
-- | Wrap nested expressions
class Monad m => MonadBlock r m | m -> r where
  wrapBlock :: r m a -> m a
