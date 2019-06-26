{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, RankNTypes, FlexibleInstances, FlexibleContexts, ScopedTypeVariables, LambdaCase #-}
{-# LANGUAGE TypeFamilies, OverloadedStrings #-}
{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Goat.Repr.Pattern
  (module Goat.Repr.Pattern, Scope(..), Var(..))
where

import Goat.Lang.Class (Selector_, Path_, (#.))
import Goat.Util ((<&>), (...))
import Bound
import Bound.Scope
import Control.Applicative (liftA2, Const(..))
import Control.Monad.Trans (lift)
import Control.Monad.State (evalState, state)
import Data.These
import Data.Align
import Data.Bifunctor
import Data.Bifunctor.Joker (Joker(..))
import Data.Bifunctor.Wrapped (WrappedBifunctor(..))
import Data.Bifoldable
import Data.Bitraversable
import Data.Discrimination
  ( Sorting(..), toMapWith
  , Grouping(..), groupWith
  )
import Data.Functor.Compose (Compose(..))
import Data.Functor.Contravariant (contramap)
import Data.Functor.Identity (Identity(..))
import Data.Functor.Plus (Alt(..), Plus(..))
import Data.Foldable (traverse_, sequenceA_)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Semigroup (Semigroup(..), Option, option)
import Data.String (IsString(..))
import Prelude.Extras (Eq1(..), Show1(..), Lift1(..))

import Debug.Trace

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

type AnnCpts a = Components ((,) a)

bindPartsFromAssocs
 :: ( Plus f, Sorting k, Ord k
    , MonadBlock (Block (AnnCpts [b]) k) m
    , Applicative h
     -- debug
    , Show k
    )
 => Assocs 
      (Trail k)
      (Int
       -> Bindings f (AnnCpts [Trail k] k) m Int)
 -> a
 -> Bindings (Parts f h) (AnnCpts [Trail k] k) m a
bindPartsFromAssocs (Assocs pairs) a
  = Match
      (Components
        (Map.intersectionWith (,) pkts pkv))
      (return a)
      (wrapPutRemaining pure bs j)
  where
  (bs, Extend pkv j)
    = bitraverseWithIndex
        (\ i (f, ne) -> (f i, ne))
        (\ i () -> pure i)
        (Extend (bindPartsFromNode crumbps) ())
  
  pkts = toMapWith (flip (<>)) tps
  (tps, crumbps)
    = foldMapWithIndex
        (\ i (t@(k :| ks), Identity f)
         -> ( [(k, [t])]
            , [case ks of
              [] -> ((k, Just i), (pure k, t, f))
              (k':ks)
               -> ((k, Nothing), (k':|ks, t, f))]
            ))
        pairs

bindPartsFromNode
 :: ( Plus f, Sorting k, Ord k
    , MonadBlock (Block (AnnCpts [a]) k) m
     -- debug
    , Show k, Show t
    )
 => [ ( (k, Maybe Int)
      , ( NonEmpty k
        , t
        , Int
           -> Bindings
                f (AnnCpts [t] k) m Int
        )
      )
    ]
 -> Map k
      ( Int
         -> Bindings
              (Parts f (Table (,) NonEmpty k))
              (AnnCpts [t] k)
              m
              Int
      , NonEmpty ()
      )
bindPartsFromNode crumbps
  = toMapWith (flip (<>))
      (foldMap
        bindPartsFromGroup
        (groupWith fst crumbps))
    
bindPartsFromGroup
 :: ( Plus f, Sorting k, Ord k
    , MonadBlock (Block (AnnCpts [a]) k) m
     -- debug
    , Show k, Show t
    )
 => [ ( (k, Maybe b)
      , ( NonEmpty k
        , t
        , Int
           -> Bindings f (AnnCpts [t] k) m Int
        )
      )
    ]
 -> [ ( k
      , ( Int
           -> Bindings
                (Parts f (Table (,) NonEmpty k))
                (AnnCpts [t] k)
                m
                Int
        , NonEmpty ()
        )
      )
    ]
bindPartsFromGroup [] = []
bindPartsFromGroup tups@(((n, (Just _)),_):_)
  = map
      (\ (_, (_, t, f))
       -> ( n
          , ( transBindings (`Parts` zero) . f
            , pure ()
            )
          ))
      tups
bindPartsFromGroup tups@(((n, Nothing),_):_)
  = [(n, (f, pure ()))]
  where
  f i
    = Match
        (Components
          (Map.intersectionWith (,) pkts pkv))
        (return i)
        (wrapPutRemaining
          (\ a -> Assocs [(n, pure a)]) bs j)
  (bs, Extend pkv j)
    = bitraverseWithIndex
        (\ i (f, ne) -> (f i, ne))
        (\ i () -> pure i)
        (Extend (bindPartsFromNode crumbps) ())
  pkts = toMapWith (flip (<>)) tps
  (tps, crumbps)
    = foldMapWithIndex
        (\ i (_, (k:|ks, t, f))
         -> ( [(k, [t])]
            , [case ks of
              [] -> ((k, Just i), (pure k, t, f))
              k':ks
               -> ((k, Nothing), (k':|ks, t, f))]
            ))
        tups
        
wrapPutRemaining
 :: ( Sorting k
    , Functor f, Functor h, Functor p
    , MonadBlock (Block (AnnCpts [c]) k) m
    )
 => (forall x. x -> h x)
 -> Bindings (Parts f (Table (,) NonEmpty k)) p m b
 -> b
 -> Bindings (Parts f h) p (Scope (Local b) m) a
wrapPutRemaining f bs b
  = hoistBindings lift
      (squashBindings
        (liftBindings2
          (\ a -> putSecond (f . wrap a))
          (Define (pure (return b)))
          bs))
 >>>= Scope . return . B . Local
  where
  putSecond
   :: (Functor f, Monad m)
   => (g a -> h (m a))
   -> Parts f g a
   -> Bindings (Parts f h) p m a
  putSecond f parts
    = Define (mapParts (fmap return) f parts)

  wrap
   :: ( Sorting k
      , MonadBlock (Block (AnnCpts [t]) k) m
      )
   => Identity a
   -> Table (,) NonEmpty k a
   -> m a
  wrap (Identity a) (Assocs ascs)
    = wrapBlock (Block (Extend c (return a)))
    where
    c = Components
          (pure . fmap return
           <$> toMapWith (flip (<>)) ascs)

mapWithIndex
 :: Traversable t
 => (Int -> a -> b) -> t a -> t b
mapWithIndex f t
  = runIdentity (traverseWithIndex (pure ... f) t)

foldMapWithIndex
 :: (Traversable t, Monoid m)
 => (Int -> a -> m) -> t a -> m
foldMapWithIndex f t
  = getConst (traverseWithIndex (Const ... f) t)

traverseWithIndex
 :: (Traversable t, Applicative f)
 => (Int -> a -> f b)
 -> t a -> f (t b)
traverseWithIndex f t
  = runJoker
 <$> bitraverseWithIndex (const pure) f (Joker t)

bitraverseWithIndex
 :: (Bitraversable t, Applicative f)
 => (Int -> a -> f c)
 -> (Int -> b -> f d)
 -> t a b -> f (t c d)
bitraverseWithIndex f g t
  = evalState
      (getCompose 
        (bitraverse
          (\ a
           -> Compose
                (state (\ i -> (f i a, i+1))))
          (\ b
           -> Compose
                (state (\ i -> (g i b, i+1))))
          t))
      0

newtype Components f a b
  = Components (Map a (f (NonEmpty b)))
  deriving (Functor, Foldable, Traversable)

deriving instance 
  (Show a, Show (f (NonEmpty b)))
   => Show  (Components f a b)

hoistComponents
 :: (forall x. f x -> g x)
 -> Components f a b -> Components g a b
hoistComponents f (Components kv)
  = Components (f <$> kv)
  
instance
  (Applicative f, Ord a)
   => Alt (Components f a) where (<!>) = mappend

instance
  (Applicative f, Ord a)
   => Plus (Components f a) where zero = mempty

instance
  (Applicative f, Ord a)
   => Monoid (Components f a b) where
  mempty = Components mempty
  Components kva `mappend` Components kvb
    = Components
        (Map.unionWith (liftA2 (<!>)) kva kvb)

--
newtype Table p f a b = Assocs [p a (f b)]
  deriving (Eq, Show)
    
assocsToMap
 :: Sorting k
 => Table (,) NonEmpty k a -> Map k (NonEmpty a)
assocsToMap (Assocs tups)
  = toMapWith (flip (<>)) tups

mapAssocs
 :: Bifunctor p
 => (f b -> g c)
 -> Table p f a b -> Table p g a c
mapAssocs f (Assocs ps)
  = Assocs (map (second f) ps)

instance
  (Bifunctor p, Functor f)
   => Functor (Table p f a) where
  fmap f p
    = unwrapBifunctor (fmap f (WrapBifunctor p))

instance
  (Bifoldable p, Foldable f)
   => Foldable (Table p f a) where
  foldMap f p = foldMap f (WrapBifunctor p)

instance
  (Bitraversable p, Traversable f)
   => Traversable (Table p f a) where
  traverse f p
    = unwrapBifunctor
   <$> traverse f (WrapBifunctor p)

instance
  (Bifunctor p, Functor f)
   => Bifunctor (Table p f) where 
  bimap f g (Assocs ps)
   = Assocs (map (bimap f (fmap g)) ps)

instance
  (Bifoldable p, Foldable f)
   => Bifoldable (Table p f) where
  bifoldMap f g (Assocs ps)
    = foldMap (bifoldMap f (foldMap g)) ps

instance 
  (Bitraversable p, Traversable f)
   => Bitraversable (Table p f) where
  bitraverse f g (Assocs ps)
    = Assocs
   <$> traverse (bitraverse f (traverse g)) ps

instance
  (Bifunctor p, Functor f)
   => Alt (Table p f a) where
  Assocs fas <!> Assocs fbs = Assocs (fas <!> fbs)

instance
  (Bifunctor p, Functor f)
   => Plus (Table p f a) where
  zero = Assocs zero

instance Monoid (Table p f a b) where
  mempty = Assocs []
  Assocs as `mappend` Assocs bs
    = Assocs (as `mappend` bs)

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

data ShadowPublic a b = ShadowPublic a b
  deriving (Functor, Foldable, Traversable)

instance Bifunctor ShadowPublic where
  bimap f g (ShadowPublic a b)
    = ShadowPublic (f a) (g b)

instance
  Monoid a => Applicative (ShadowPublic a) where
  pure = ShadowPublic mempty
  ShadowPublic a1 f <*> ShadowPublic a2 b
    = ShadowPublic (a1 `mappend` a2) (f b)  

--
type Trail a = NonEmpty a

fromTrail :: Selector_ r => Trail Ident -> r
fromTrail (n NonEmpty.:| ns) = go n ns ""
  where
  go n [] s = s #. fromIdent n
  go n (n':ns) s = go n' ns (s #. fromIdent n)

fromViewTrails
 :: Path_ r => View (Trail Ident) -> r
fromViewTrails
  = \case
    Tag (Left (Local (n NonEmpty.:| [])))
     -> fromIdent n
    
    Tag (Left (Local (n NonEmpty.:| (n':ns))))
     -> go n' ns (fromIdent n)
    
    Tag (Right (Public (n NonEmpty.:| ns)))
     -> go n ns ""
  where
  go n [] s = s #. fromIdent n
  go n (n':ns) s = go n' ns (s #. fromIdent n)
--

type View = Tag Local Public
type Assocs = Table (,) Identity
type AssocAnns a = Table ((,,) a) Identity
type AssocViews = Table (,) View
type ShadowView a = Tag Local (ShadowPublic a)
type AssocShadows a = Table (,) (ShadowView a)

newtype Ident = Ident Text
  deriving (Eq, Ord, Show)

showIdent :: Ident -> String
showIdent (Ident t) = Text.unpack t

fromIdent :: IsString a => Ident -> a
fromIdent = fromString . showIdent

instance Grouping Ident where
  grouping = contramap showIdent grouping

instance Sorting Ident where
  sorting = contramap showIdent sorting

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
     -> instantiateBindings (get (k p m)) bs
    
    Index bs
     -> let
        Parts pv fv
          = instantiateBindings
              (get (foldMap pure pv)) bs
        in fv
  
  where
  instantiateBindings
   :: forall f b
    . Functor f
   => (b -> m a)
   -> Bindings f p (Scope b m) a
   -> f (m a)
  instantiateBindings get bs
    = subst <$> substituteBindings k' bs
    where
    k' p s = map lift (k p (subst s))
    subst = instantiate get
    
  --maybeGet (v, vs) (Local (Just i)) = vs !! i
  --maybeGet (v, vs) (Local Nothing) = v
  get vs (Local i) = vs !! i
    

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
  second' f = mapParts id f
  --second' f (Parts pa fa) = Parts pa (f fa)

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
  first' f = mapParts f id
  -- (Parts pa fa) = Parts (f pa) fa

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
  both' f g h  = traverseParts (f h) (g h)
    -- = Parts <$> f h pa <*> g h fa

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
  first' f pfa ga = mapParts id (`f` ga) pfa
  -- first' f (Parts pa fa) ga = Parts pa (f fa ga)
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
  second' f fa = mapParts id (f fa)
  --second' f fa (Parts pa ga) = Parts pa (f fa ga)

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
  (Alt f, Functor p, Monad m)
   => Semigroup (Bindings f p m a)
  where (<>) = (<!>)

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

{-
-- A lifted compose type like 'Data.Functor.Compose'
-- with some different instances

newtype Inside f r a
  = Inside { getInside :: r (f a) }
  deriving (Functor, Foldable, Traversable)

mapInside
  :: Functor r
  => (f a -> g b)
  -> Inside f r a -> Inside g r b
mapInside f (Inside r) = Inside (f <$> r)

instance 
  (Applicative f, Applicative r)
   => Applicative (Inside f r)
  where
  pure a = Inside (pure (pure a))
  Inside rff <*> Inside rfa
    = Inside ((<*>) <$> rff <*> rfa)

instance
  (Functor f, Alt r) => Alt (Inside f r) where
  Inside a <!> Inside b = Inside (a <!> b)

instance
  (Functor f, Plus r) => Plus (Inside f r) where
  zero = Inside zero

instance
  Monoid (r (f a)) => Monoid (Inside f r a)
  where
  mempty = Inside mempty
  Inside a `mappend` Inside b
    = Inside (a `mappend` b) 
-}

-- A lifted product like 'Data.Functor.Product'

data Parts f g a = Parts (f a) (g a)
  deriving (Functor, Foldable, Traversable)

traverseParts
 :: Applicative h
 => (f a -> h (f' b))
 -> (g a -> h (g' b))
 -> Parts f g a -> h (Parts f' g' b)
traverseParts f g (Parts fa ga)
  = Parts <$> f fa <*> g ga

mapParts
 :: (f a -> f' b)
 -> (g a -> g' b)
 -> Parts f g a -> Parts f' g' b
mapParts f g
  = runIdentity
  . traverseParts (pure . f) (pure . g)

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

--
newtype Tag f g a
  = Tag { getTag :: Either (f a) (g a) }

traverseTag
 :: Applicative h
 => (f a -> h (f' b))
 -> (g a -> h (g' b))
 -> Tag f g a -> h (Tag f' g' b)
traverseTag f g (Tag e)
  = Tag <$> bitraverse f g e

mapTag
 :: (f a -> f' b)
 -> (g a -> g' b)
 -> Tag f g a -> Tag f' g' b
mapTag f g
  = runIdentity . traverseTag (pure . f) (pure . g)

instance
  (Functor f, Functor g) => Functor (Tag f g) where
  fmap f (Tag e) = Tag (bimap (fmap f) (fmap f) e)

instance
  (Foldable f, Foldable g) => Foldable (Tag f g) 
  where
  foldMap f (Tag e)
    = bifoldMap (foldMap f) (foldMap f) e

instance
  (Traversable f, Traversable g)
   => Traversable (Tag f g) where
  traverse f (Tag e)
    = Tag <$> bitraverse (traverse f) (traverse f) e

-- |
newtype Block p a m b
  = Block
      (Extend
        (p a)
        (Scope
          (Super Int) (Scope (Public a) m) b)
        (m b))

wrapExtend
 :: MonadBlock (Block p a) m
 => p a (Scope (Super Int) (Scope (Public a) m) b)
 -> m b
 -> m b
wrapExtend f m
  = wrapBlock (Block (Extend f m))

-- | Wrap nested expressions
class Monad m => MonadBlock r m | m -> r where
  wrapBlock :: r m a -> m a
