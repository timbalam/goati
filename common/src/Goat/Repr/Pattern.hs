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
import Data.Discrimination
  (Grouping(..), runGroup, nubWith)
import Data.Foldable (traverse_, sequenceA_)
-- import Data.Traversable (mapAccumL)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map 
import Data.Map (Map)
import qualified Data.Text as Text
import Data.Text (Text)
--import Data.Maybe (fromMaybe)
import Data.Semigroup (Semigroup(..), Option, option)
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

type Trail a = NonEmpty a
newtype Assocs p a b = Assocs [p a b]
instance Bifunctor p => Functor (Assocs p a) where 
  fmap f (Assocs ps) = Assocs (map (second f) ps)
instance Bifunctor p => Alt (Assocs p a) where
  Assocs fas <!> Assocs fbs = Assocs (fas <!> fbs)
instance Bifunctor p => Plus (Assocs p a) where
  zero = Assocs zero
type Cpts = Assocs (,)
type TagCpts k = Assocs ((,,) [Trail k]) k

bindPartsFromAssocs
 :: ( Plus f, Grouping k
    , MonadBlock (Block (Cpts k)) m
    , Applicative h
    )
 => Cpts
      (Trail k)
      (Int -> Bindings f (TagCpts k) m Int)
 -> a -> Bindings (Parts f h) (TagCpts k) m a
bindPartsFromAssocs (Assocs ps) a
  = Match
      (Assocs p)
      (return a)
      (wrapPutRemaining pure bs)
  where
  (p, bs) = bindPartsFromNode crumbps
  crumbps
    = [ (NonEmpty.head t, (NonEmpty.tail t, t, f))
      | (t, f) <- ps
      ]
  
  
  bindPartsFromLeaf
   :: ( Plus f, Grouping k
      , MonadBlock (Block (Cpts k)) m
      )
   => Int
   -> [ ( k
        , ( [k]
          , Trail k
          , Int -> Bindings f (TagCpts k) m Int
          )
        )
      ]
   -> ( [([Trail k], k, ())]
      , Bindings
          (Parts f (Cpts k)) (TagCpts k) m Int
      )
  bindPartsFromLeaf i crumbps
    = (p, bs')
    where
    bs' = transBindings (`Parts` Assocs []) bs
    (p, bs)
      = foldMap 
          (\ (k, (_, t, f))
           -> ([([t], k, ())], f i))
          crumbps
  
  bindPartsFromNode
   :: [ ( k
        , ( [k]
          , Trail k
          , Int -> Bindings f (TagCpts k) m Int
          )
      ]
   -> ( [([Trail k], k, ())]
      , Bindings
          (Parts f (TagCpts k)) (TagCpts k) m Int
      )
  bindPartsFromNode tups
    = foldMap id
        (zipWith3
          (bindPartsFromGroup . fst)
          (nubWith fst crumbps)
          [0..]
          (runGroup grouping crumbps))
      
  bindPartsFromGroup
   :: ( Plus f, Grouping k
      , MonadBlock (Block (Cpts k)) m
      )
   => k
   -> Int
   -> [ ( [k]
        , Trail k
        , Int -> Bindings f (TagCpts k) m Int
        )
      ]
   -> ( [([Trail k], k, ())]
      , Bindings
          (Parts f (Cpts k)) (TagCpts k) m Int
      )
  bindPartsFromGroup n i tups
    = foldMap id
        (zipWith
          (\ crumbps (isnd, _)
           -> if isnd then
              bindPartsWrap
                (bindPartsFromNode crumbps)
              else
              bindPartsFromLeaf i crumbps)
        (runGroup grouping lfndcrumbps)
        (nubWith fst lfndcrumbps))
    
    where
    bindPartsWrap (p, bs)
      = ( [ts, n, ()]
        , Match (Assocs p) (return i)
            (wrapPutRemaining
              (Assocs . pure . (,) n) bs)
        )
    
    (ts, lfndcrumbps)
      = traverse
          (\case
            ([], t, f)
             -> ([t], (False, (n, ([], t, f))))
            
            (k:ks, t, f)
             -> ([t], (True, (k, (ks, t, f)))))
          tups
        
wrapPutRemaining
 :: ( Functor f, Functor g
    , Functor h, Functor p
    , MonadBlock (Block g) m
    )
 => (forall x. x -> h x)
 -> Bindings (Parts f g) p m i
 -> Bindings
      (Parts f h)
      p
      (Scope (Local (Maybe i)) m)
      a
wrapPutRemaining f bs
  = embedBindings 
      (putSecond (f . wrap (Local Nothing)))
      (hoistBindings lift bs
        >>>= Scope . return . B . Local . Just)
  where
  putSecond
   :: (Functor f, Monad m)
   => (g a -> h (m a))
   -> Parts f g a
   -> Bindings (Parts f h) p m a
  putSecond f (Parts fa ga)
    = Define
        (Parts
          (return <$> fa) (f ga))

  wrap
   :: (Functor g, MonadBlock (Block g) m)
   => b -> g a -> Scope b m a
  wrap b ga
    = Scope
        (wrapBlock
          (Block 
            (Extend
              (return . F . return <$> ga)
              (pure (return (B b))))))

{-
type Split f = Parts f Maybe
type Cpts f = Inside (Ambig f) (Map Text)
type BlockCpts f = Block (Cpts f)

bindPartsFromAssocs
 :: ( Plus f, Applicative g
    , Applicative h, Traversable h
    , Applicative u, MonadBlock (BlockCpts u) m
    )
 => Assocs
      (Ambig h (Int -> Bindings f (Cpts h) m Int))
 -> a -> Bindings (Parts f g) (Cpts h) m a
bindPartsFromAssocs (Assocs r k) a
  = fst
      (bindPartsFromNode
        (bindPaths
          . fmap bindPartsFromLeaf
          . k
         <$> r))
      a
  where
  bindPaths
   :: ( Plus f, Applicative h, Applicative u
      , MonadBlock (BlockCpts u) m
      )
   => Paths (Map Text)
        ( Int -> Bindings (Split f) (Cpts h) m Int
        , Ambig h ()
        )
   -> ( Int -> Bindings (Split f) (Cpts h) m Int
      , Ambig h ()
      )
  bindPaths
    = merge
    . iterPaths
        (bindPartsFromNode . fmap merge)
  
  merge :: Semigroup m => These m m -> m
  merge = these id id (<>)
  
  bindPartsFromLeaf
   :: (Plus f, Traversable g, Functor p, Monad m)
   => g (Int -> Bindings f p m Int)
   -> ( Int -> Bindings (Parts f Maybe) p m Int
      , g ()
      )
  bindPartsFromLeaf t
    = (transBindings (`Parts` Nothing) . f, t')
    where
    (f, t') = traverse (\ f -> (f, ())) t

  bindPartsFromNode
   :: ( Plus f, Applicative g, Applicative h
      , Applicative u, MonadBlock (BlockCpts u) m
      )
   => Map Text
        ( Int -> Bindings (Split f) (Cpts h) m Int
        , Ambig h ()
        )
   -> ( a -> Bindings (Parts f g) (Cpts h) m a
      , Ambig h ()
      )
  bindPartsFromNode r
    = matchEtcFromPair patternAnnots
        (componentsAssocsFromNode r)
    where
    matchEtcFromPair
     :: Monad m
     => (Cpts h () -> b)
     -> ( Cpts h ()
        , Bindings f (Cpts h) (Scope (Local Int) m) a
        )
     -> (a -> Bindings f (Cpts h) m a, b)
    matchEtcFromPair f (p, bs) =
      (\ a -> Match p (return a) bs, f p)
    
    patternAnnots (Inside kv)
      = Ambig
          (pure 
            (traverse_
              (\ (Ambig ne) -> sequenceA_ ne)
              kv))

componentsAssocsFromNode
 :: ( Plus f, Applicative g, Functor p
    , Applicative u, MonadBlock (BlockCpts u) m
    )
 => Map Text
      ( Int -> Bindings (Split f) p m Int
      , Ambig h ()
      )
 -> ( Cpts h ()
    , Bindings (Parts f g) p (Scope (Local Int) m) b
    )
componentsAssocsFromNode r
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
 :: ( Plus f, Applicative g, Applicative h
    , Functor p, MonadBlock (BlockCpts h) m
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
    :: (Applicative t, MonadBlock (BlockCpts t) m)
    => Parts f (Map Text) a
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
-}

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

{-
newtype Ambig f a = Ambig (NonEmpty (f a))
  deriving
    (Functor, Foldable, Traversable)

mapAmbig
 :: (f a -> g b)
 -> Ambig f a -> Ambig g b
mapAmbig f (Ambig ne) = Ambig (f <$> ne)

instance Applicative f => Applicative (Ambig f) where
  pure a = Ambig (pure (pure a))
  Ambig fs <*> Ambig as
    = Ambig ((<*>) <$> fs <*> as)

instance Functor f => Alt (Ambig f) where
  Ambig as <!> Ambig bs = Ambig (as <!> bs)

instance Semigroup (Ambig f a) where
  Ambig as <> Ambig bs = Ambig (as <> bs)


-- | Match data to selected parts of a value
data Assocs a
  = forall x
  . Assocs
      (Map Text x)
      (x -> Paths (Map Text) a)

sendAssocs
 :: Map Text a -> Assocs a
sendAssocs r = Assocs r Leaf

wrapAssocs
 :: Map Text (Paths (Map Text) a) -> Assocs a
wrapAssocs r = Assocs r id

instance Functor Assocs where
  fmap f (Assocs r k) = Assocs r (fmap f . k)

instance Foldable Assocs where
  foldMap f (Assocs r k) = foldMap (foldMap f . k) r

instance Traversable Assocs where
  traverse f (Assocs r k)
    = Assocs
   <$> traverse (traverse f . k) r
   <*> pure id

instance Align Assocs where
  nil = Assocs mempty id
  align (Assocs ra ka) (Assocs rb kb)
    = Assocs
        (align ra rb)
        (bicrosswalkPaths ka kb)


-- | Declare assosiations between local and public paths and values

data Declares a
  = forall x
  . Declares
      (Local (Map Text x))
      (Public (Map Text x))
      (x -> Paths (Map Text) a)

wrapLocal
 :: Map Text (Paths (Map Text) a) -> Declares a
wrapLocal kv = Declares (Local kv) mempty id

wrapPublic
 :: Map Text (Paths (Map Text) a) -> Declares a
wrapPublic kv
  = Declares mempty (Public kv) id

instance Functor Declares where
  fmap f (Declares lr pr k)
    = Declares lr pr (fmap f . k)

instance Foldable Declares where
  foldMap f (Declares lr pr k)
    = foldMap (foldMap (foldMap f . k)) lr
    `mappend`
      foldMap (foldMap (foldMap f . k)) pr

instance Traversable Declares where
  traverse f (Declares lr pr k)
    = Declares
   <$> traverse (traverse (traverse f . k)) lr
   <*> traverse (traverse (traverse f . k)) pr
   <*> pure id

instance Align Declares where
  nil = Declares mempty mempty id
  
  align (Declares lra pra ka) (Declares lrb prb kb)
    = Declares 
        (liftA2 align lra lrb)
        (liftA2 align pra prb)
        (bicrosswalkPaths ka kb)

-- | Associate a set of fields with values, possibly ambiguously
data Paths r a
  = forall x
  . Node (r x) (x -> Paths r a)
  | Leaf a
  | forall x
  . Overlap (r x) (x -> Paths r a) a

sendPaths :: r a -> Paths r a
sendPaths r = Node r Leaf

wrapPaths :: r (Paths r a) -> Paths r a
wrapPaths r = Node r id

alignPathsWith
 :: Align r
 => (These a b -> c)
 -> Paths r a -> Paths r b -> Paths r c
alignPathsWith
  = alignpw
  where
  alignnw
   :: Align r 
   => (These a b -> c)
   -> r x -> (x -> Paths r a)
   -> r y -> (y -> Paths r b)
   -> (forall xx
        . r xx
       -> (xx -> Paths r c)
       -> p)
   -> p
  alignnw f ra ka rb kb g
    = g (align ra rb)
        (fmap f . bicrosswalkPaths ka kb)
  
  alignpw
   :: Align r
   => (These a b -> c)
   -> Paths r a
   -> Paths r b
   -> Paths r c
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

bicrosswalkPaths
 :: Align r 
 => (a -> Paths r c)
 -> (b -> Paths r d)
 -> These a b
 -> Paths r (These c d)
bicrosswalkPaths f g
  = \case
    This a -> This <$> f a
    That b -> That <$> g b
    These a b -> alignPathsWith id (f a) (g b)

iterPaths
 :: Functor r
 => (r (These a b) -> b)
 -> Paths r a
 -> These a b
iterPaths
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
   -> (x -> Paths r a)
   -> b
  iterNode kf r k = kf (iterPaths kf . k <$> r)

instance Functor (Paths r) where
  fmap f (Node r k)
    = Node r (fmap f . k)
  fmap f (Leaf a)
    = Leaf (f a)
  fmap f (Overlap r k a)
    = Overlap r (fmap f . k) (f a)

instance Foldable r => Foldable (Paths r) where
  foldMap f (Node r k)
    = foldMap (foldMap f . k) r
  foldMap f (Leaf a)
    = f a
  foldMap f (Overlap r k a)
    = foldMap (foldMap f . k) r `mappend` f a

instance
  Traversable r => Traversable (Paths r)
  where
  traverse
    = traverse'
    where
    traverseNode
     :: (Traversable r, Applicative f)
     => (a -> f b)
     -> r x -> (x -> Paths r a)
     -> (forall xx
          . r xx
         -> (xx -> Paths r b)
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
-}

-- | 'Bindings f p m a' binds expressions of type 'm a'
-- inside a container 'f' to patterns of type 'p'. 
data Bindings f p m a
  = Define (f (m a))
  | Match (p ()) (m a)
      (Bindings f p (Scope (Local (Maybe Int)) m) a)
  | Index
      (Bindings (Parts p f) p
        (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

substituteBindings
 :: forall f p m a
  . (Functor f, Functor p, Foldable p, Monad m)
 => (p () -> m a -> (m a, [m a]))
 -> Bindings f p m a -> f (m a)
substituteBindings k
  = \case
    Define fm
     -> fm
    
    Match p m bs
     -> instantiateBindings (maybeGet (k p m)) bs
    
    Index bs
     -> let
        Parts pv fv
          = instantiateBindings
              (get (foldMap pure pv)) bs
        in fv
  
  where
  instantiateBindings get bs
    = subst <$> substituteBindings k' bs
    where
    k' p s = bimap lift (map lift) (k p (subst s))
    subst = instantiate get
    
  maybeGet (v, vs) (Local (Just i)) = vs !! i
  maybeGet (v, vs) (Local Nothing) = v
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

mapParts
 :: (f a -> f' b)
 -> (g a -> g' b)
 -> Parts f g a -> Parts f' g' b
mapParts f g (Parts fa ga) = Parts (f fa) (g ga)

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
newtype Tag f g a = Tag (Either (f a) (g a))

mapTag
 :: (f a -> f' b)
 -> (g a -> g' b)
 -> Tag f g a -> Tag f' g' b
mapTag f g (Tag e) = Tag (bimap f g e)

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
type Ident = Text

showIdent :: Ident -> String
showIdent = Text.unpack

newtype Block f m a
  = Block
      (Extend f
        (Scope (Super Ident)
          (Scope (Public Ident) m) a)
        (Maybe (m a)))

-- | Wrap nested expressions
class Monad m => MonadBlock r m | m -> r where
  wrapBlock :: r m a -> m a
