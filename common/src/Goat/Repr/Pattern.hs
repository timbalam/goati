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
import qualified Data.Map as Map 
import qualified Data.Text as Text
import Data.Maybe (fromMaybe)
import Data.Semigroup
import qualified Data.Monoid as Monoid (Alt(..))
import Data.Void (Void, absurd)
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
 :: Monad m
 => (forall x. x -> Bindings f (Components ()) m x)
 -> Bindings (Parts f Identity) (Components ()) m a
 -> Bindings f (Components ()) m a
bindRemaining f =
  embedBindings
    (\ (Parts fm (Identity m)) ->
      Define (return <$> fm) <!> f (return m))
    
ignoreRemaining
 :: Monad m
 => Bindings (Parts f g) (Components ()) m a
 -> Bindings f (Components ()) m a
ignoreRemaining = transBindings (\ (Parts fm _) -> fm)

type BindMatchParts f m =
  Int -> Bindings (Parts f Maybe) (Components ()) m Int
 
bindPartsFromMatches
 :: (Plus f, MonadBlock (Abs Components) m, Applicative h)
 => Matches (Int -> Bindings f (Components ()) m Int)
 -> a
 -> Bindings (Parts f h) (Components ()) m a
bindPartsFromMatches (Matches r k) a =
  bindPartsFromNode
    (bindAssigns . k <$> r)
    a
  where
    bindAssigns
     :: Assigns (NonEmpty (Int -> Bindings f p m Int))
     -> ([()], Int -> Bindings (Parts f Maybe) p m Int)
    bindAssigns =
      merge .
      iterAssigns
        bindPartsFromLeaf
        (\ r k ->
          bindPartsFromNode (pure . merge . k <$> r))
  
    merge
     :: Monoid m => These ([()], m) m -> ([()], m)
    merge (This p) = p
    merge (That m) = (pure (), m)
    merge (These (f, m) m') = (f <|> pure (), m `mappend` m')
    
    
    bindPartsFromLeaf
     :: (Plus f, Monad m)
     => NonEmpty (Int -> Bindings f p m Int)
     -> ([()], Int -> Bindings (Parts f Maybe) p m Int)
    bindPartsFromLeaf t = (f, bindFirstPart)
      where
        (Monoid.Alt f, k) = foldMap pure t
        bindFirstPart i = transBindings (`Parts` Nothing) (k i)

    bindPartsFromNode
      :: ( Plus f, MonadBlock (Abs Components) m
         , Applicative h
         )
      => Map Text ([()], BindMatchParts f m)
      -> a
      -> Bindings (Parts f h) (Components ()) m a
    bindPartsFromNode r a = 
      case componentsFromNode r of
        (p, x) -> Let p (return a) x 

componentsFromNode
 :: ( Plus f, MonadBlock (Abs Components) m
    , Applicative h
    )
 => Map Text ([()], BindMatchParts f m)
 -> ( Components ()
    , Bindings (Parts f h)
        (Components ())
        (Scope (Local Int) m)
        b
    )
componentsFromNode r = (p, xm')
  where
    x = Extend r ([], bindSecondPart)
    p = Inside (fst <$> x)
    xm = mapWithIndex (\ i (_, f) -> f i) x
    xm' =
      hoistBindings lift (bindPartsFromExtension xm)
      >>>= \ i -> Scope (return (B (Local i)))
    
    bindSecondPart
     :: (Plus f, Monad m) => a -> Bindings f Maybe m a
    bindSecondPart i = Define (Parts zero (pure (return i)))

bindPartsFromExtension
 :: (Plus f, MonadBlock (Abs Components) m, Applicative h)
 => Extend
     (Map Text)
     (Bindings (Parts f Maybe) (Components ()) m a)
 -> Bindings (Parts f h) (Components ()) m a
bindPartsFromExtension (Extend r m) =
  embedBindings
    wrapAndbindParts
    (liftBindings2 mergeParts r' m)
  where
    r' =
      foldMapWithKey (transBindings . hoistSnd . partToField) r
  
    mergeParts
      :: Alt f
      => Parts f (Many (Map Text)) a -> Parts f Maybe a
      -> Parts f Components a
    mergeParts =
      hoistBoth (<!>) partsToComponents
    
    partsToComponents
     :: Many (Map Text) a -> Maybe a -> Components a
    partsToComponents (Inside rm) m =
      Inside (Extend rm (maybe empty [] m))
  
    partToField
     :: Text -> Maybe a -> Many (Map Text) a
    partToField n b =
      maybe mempty (Inside . Map.singleton n . pure) b
    
    wrapAndBindParts
     :: ( Functor f, Functor r
        , MonadBlock (Abs r) m
        , Applicative h
        )
     => Parts f r a -> Bindings (Parts f h) m a
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
  
-- | Access control wrappers
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)

instance Applicative Public where
  pure = Public
  Public f <*> Public a = Public (f a)
  
newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)

instance Applicative Local where
  pure = Local
  Local f <*> Local a = Local (f a)
  
newtype Match a = Match { getMatch :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)

instance Applicative Match  where
  pure = Match
  Match f <*> Match a = Match (f a)
  
-- | Match data to selected parts of a value
data Matches a =
  forall x .
    Matches
      (Match (Map Text x))
      (x -> Assigns (Map Text) (NonEmpty a))

sendMatches
 :: Map Text a -> Matches a
sendMatches r = Matches (Match r) (Leaf . pure)

wrapMatches
 :: Map Text (Assigns (Map Text) a) -> Matches a
wrapMatches r = Matches (Match r) (fmap pure)

instance Functor Matches where
  fmap f (Matches r k) =
    Matches r (fmap (fmap f) . k)

instance Foldable Matches where
  foldMap f (Matches r k) =
    foldMap (foldMap (foldMap (foldMap f) . k)) r

instance Traversable Matches where
  traverse f (Matches r k) =
    Matches <$> 
      traverse (traverse (traverse (traverse f) . k)) r <*>
      pure id
      
instance Alt Matches where
  Matches ra ka <!> Matches rb kb =
    Matches
      (liftA2 align ra rb)
      (these id id (<!>) <$> bicrosswalkAssigns ka kb)

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
      (these id id (<!>) <$> bicrosswalkAssigns ka kb)

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
 :: (a -> b)
 -> (forall x . r x -> (x -> These b c) -> c)
 -> Assigns r a
 -> These b c
iterAssigns = iterAssigns' where
  iterAssigns'
   :: (a -> b)
   -> (forall x . r x -> (x -> These b c) -> c)
   -> Assigns r a
   -> These b c
  iterAssigns' ka kf (Leaf a) = This (ka a)
  iterAssigns' ka kf (Node r k) = That (iterNode ka kf r k)
  iterAssigns' ka kf (Overlap r k a) =
    These (ka a) (iterNode ka kf r k)
  
  iterNode
   :: (a -> b)
   -> (forall x . r x -> (x -> These b c) -> c)
   -> r y
   -> (y -> Assigns r a)
   -> c
  iterNode ka kf r k = kf r (iterAssigns ka kf . k)

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
  | Let
      p
      (Scope (Local Int) m a)
      (Bindings f p (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

-- | Higher order map over expression type.
hoistBindings
 :: (Functor f, Functor m)
 => (forall x . m x -> n x)
 -> Bindings f p m a -> Bindings f p n a
hoistBindings f (Define fm) = Define (f <$> fm)
hoistBindings f (Let p m t) =
  Let p (hoistScope f m) (hoistBindings (hoistScope f) t)

-- | Higher order map over container type.
transBindings
 :: (forall x . f x -> g x)
 -> Bindings f p m a -> Bindings g p m a
transBindings f (Define fm) = Define (f fm)
transBindings f (Let p m t) = Let p m (transBindings f t)

-- | Higher order traverse over container type.
transverseBindings
 :: Functor h
 => (forall x . f x -> h (g x))
 -> Bindings f p m a -> h (Bindings g p m a)
transverseBindings f (Define fm) = Define <$> f fm
transverseBindings f (Let p m t) =
  Let p m <$> transverseBindings f t

-- | Higher order applicative function lifting over container type.
liftBindings2
 :: (Functor f, Functor g, Monad m)
 => (forall x . f x -> g x -> h x)
 -> Bindings f p m a -> Bindings g p m a -> Bindings h p m a
liftBindings2 f (Define fm) (Define gm) = Define (f fm gm)
liftBindings2 f (Let p m tf) (Define gm) =
  Let p m (liftBindings2 f tf (hoistBindings lift (Define gm)))
liftBindings2 f tf (Let p m tg) =
  Let p m (liftBindings2 f (hoistBindings lift tf) tg)

-- | Higher order bind over container type.
embedBindings
 :: (Functor g, Monad m)
 => (forall x . f x -> Bindings g p m x)
 -> Bindings f p m a -> Bindings g p m a
embedBindings f (Define fm) = f fm >>>= id
embedBindings f (Let p m t) =
  Let p m (embedBindings (hoistBindings lift . f) t)

-- | Higher order join over container type
squashBindings
 :: (Functor f, Monad m)
 => Bindings (Bindings f p m) p m a -> Bindings f p m a
squashBindings = embedBindings id

instance Functor f => Bound (Bindings f p) where
  Define fm     >>>= f = Define ((>>= f) <$> fm)
  Let p m t >>>= f = Let p (m >>>= f) (t >>>= lift . f)

instance (Alt f, Monad m) => Alt (Bindings f p m) where
  a <!> b = liftBindings2 (<!>) a b 

instance (Plus f, Monad m) => Plus (Bindings f p m) where
  zero = Define zero

instance (Plus f, Monad m) => Monoid (Bindings f p m a) where
  mempty = zero
  mappend a b = a <!> b
  
  
-- 
type Components = Many (Extend (Map Text))
type Multi = Inside NonEmpty
type Many = Inside []

-- Combine an additional 'leftover' value to a container 'r'.
data Extend r a = Extend (r a) a
  deriving (Functor, Foldable, Traversable)

hoistExtend
 :: (forall x . q x -> r x) -> Extend q a -> Extend r a
hoistExtend f (Extend r a) = Extend (f r) a

instance (Monoid (r a), Monoid a) => Monoid (Extend r a) where
  mempty = Extend mempty mempty
  Extend r1 a1 `mappend` Extend r2 a2 =
    Extend (r1 `mappend` r2) (a1 `mappend` a2)

-- A lifted compose type like 'Data.Functor.Compose'
-- with some different instances

newtype Inside f r a = Inside { getInside :: r (f a) }
  deriving (Functor, Foldable, Traversable)

hoistInside
 :: Functor r
 => (forall x. f x -> g x)
 -> Inside f r a -> Inside g r a
hoistInside f (Inside r) = Inside (f <$> r)

hoistOutside
 :: (forall x. q x -> r x)
 -> Inside f q a -> Inside f r a
hoistOutside f (Inside r) = Inside (f r)
  
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

data Parts f g a = Parts (f a) (g a) deriving Functor

hoistFirst
 :: (forall x . f x -> f' x) -> Parts f g a -> Parts f' g a
hoistFirst f (Parts fa ga) = Parts (f fa) ga

hoistSecond
 :: (forall x . g x -> g' x) -> Parts f g a -> Parts f g' a
hoistSecond f (Parts fa ga) = Parts fa (f ga)

hoistParts
 :: (forall x . f x -> f' x)
 -> (forall x . g x -> g' x)
 -> Parts f g a -> Parts f' g' a
hoistParts f g (Parts fa ga) = Parts (f fa) (g ga)

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
type Block r m a = Bindings r (r ()) m a

newtype Abs r m a = Abs (Block r (Scope (Public Ident) m) a)
  deriving (Functor, Foldable, Traversable)

hoistAbs
 :: (Functor r, Functor m)
 => (forall x . m x -> n x)
 -> Abs r m a -> Abs r n a
hoistAbs f (Abs b) = Abs (hoistBindings (hoistScope f) b)

instance Functor r => Bound (Abs r) where
  Abs b >>>= f = Abs (b >>>= lift . f)

-- | Wrap nested expressions
class Monad m => MonadBlock r m | m -> r where
  wrapBlock :: r m a -> m a
