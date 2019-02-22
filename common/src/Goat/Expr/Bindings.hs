{-# LANGUAGE TypeFamilies, FlexibleInstances, ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveTraversable, RankNTypes #-}
module Goat.Expr.Bindings
  where

import Goat.Lang.Ident (Ident, IsString(..))
import Goat.Lang.Let (Let_(..))
import Goat.Lang.Field (Field_(..))
import Control.Monad (ap, liftM, join)
import Control.Monad.Free
import Data.Bifunctor
import Data.Profunctor
import qualified Data.Map as Map
import Data.Align (Align(..), bicrosswalk)
import Data.Semigroup
import Data.These (These(..), mergeTheseWith, mergeThese)
import Data.Void (absurd)

--infixl 5 :?

newtype Components a = Components (Map.Map Ident a)
  deriving (Align, Functor, Foldable, Traversable)

singleton :: Ident -> a -> Components a
singleton k a = Components (Map.singleton k a)

empty :: Components a
empty = Components Map.empty

-- | A possibly ambiguous value with two states,
-- a leaf / final type 'b' and
-- an node / extensible nested type 'r'.
data Nested r a =
    forall x . Node (r x) (x -> Nested r a)
  | Leaf a
  | forall x . NodeAndLeaf (r x) (x -> Nested r a) a

sendPaths :: r a -> Nested r a
sendPaths r = Node r Leaf

wrapPaths :: r (Nested r a) -> Nested r a
wrapPaths r = Node r id

instance Functor (Nested r) where
  fmap f (Node r k) = Node r (fmap f . k)
  fmap f (Leaf a) = Leaf (f a)
  fmap f (NodeAndLeaf r k a) = NodeAndLeaf r (fmap f . k) (f a)

instance Align r => Align (Nested r) where
  nil = Node nil absurd
  
  align = align' where
    alignNodes
     :: Align r 
     => r x -> (x -> Nested r a)
     -> r y -> (y -> Nested r b)
     -> (forall xx . r xx -> (xx -> Nested r (These a b)) -> p)
     -> p
    alignNodes ra ka rb kb =
      runC (alignWith (bicrosswalk ka kb) (sendC ra) (sendC rb))
     --f (align ra rb) (mergeTheseWith ka kb align)
      
    align' (Node ra ka)          (Node rb kb)          =
      alignNodes ra ka rb kb Node
    align' (Node ra ka)          (Leaf b)              =
      NodeAndLeaf ra (fmap This . ka) (That b)
    align' (Node ra ka)          (NodeAndLeaf rb kb b) =
      alignNodes ra ka rb kb NodeAndLeaf (That b)
    align' (Leaf a)              (Node rb kb)          =
      NodeAndLeaf rb (fmap That . kb) (This a)
    align' (Leaf a)              (Leaf b)              =
      Leaf (These a b)
    align' (Leaf a)              (NodeAndLeaf rb kb b) =
      NodeAndLeaf rb (fmap That . kb) (These a b)
    align' (NodeAndLeaf ra ka a) (Node rb kb)          =
      alignNodes ra ka rb kb NodeAndLeaf (This a)
    align' (NodeAndLeaf ra ka a) (Leaf b)              =
      NodeAndLeaf ra (fmap This . ka) (These a b)
    align' (NodeAndLeaf ra ka a) (NodeAndLeaf rb kb b) =
      alignNodes ra ka rb kb NodeAndLeaf (These a b)

instance Foldable r => Foldable (Nested r) where
  foldMap f (Node r k) = foldMap (foldMap f . k) r
  foldMap f (Leaf a) = f a
  foldMap f (NodeAndLeaf r k a) =
    foldMap (foldMap f . k) r `mappend` f a

instance Traversable r => Traversable (Nested r) where
  traverse f = traverse' where
    traverseNode
      :: (Traversable r, Applicative f)
      => (a -> f b)
      -> r x -> (x -> Nested r a)
      -> (forall xx . r xx -> (xx -> Nested r b) -> p)
      -> f p
    traverseNode f r k g =
      g <$> traverse (traverse f . k) r <*> pure id
    
    traverse' (Node r k)          =
      traverseNode f r k Node
    traverse' (Leaf a)              =
      fmap Leaf (f a)
    traverse' (NodeAndLeaf r k a) =
      traverseNode f r k NodeAndLeaf <*> f a

instance (Align r, Semigroup a) => Semigroup (Nested r a) where
  a <> b = alignWith (mergeThese (<>)) a b


-- | Construct a binding
data Binding r a b =
  forall x . Binding (a -> r x) (x -> b)

sendBinding :: (a -> r b) -> Binding r a b
sendBinding f = Binding f id

binding
 :: Binding r a b -> a -> C r b
binding (Binding f k) a = fmap k (sendC (f a))

instance Functor (Binding r a) where fmap = rmap

instance Profunctor (Binding r) where
  lmap f (Binding c k) = Binding (c . f) k
  rmap f (Binding c k) = Binding c (f . k)
  

-- | LHS bindings
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Semigroup)

newtype Local a = Local { getLocal :: a }
  deriving (Functor, Semigroup)
  
type Visibility a = Either (Public a) (Local a)

data Reference a = Starts | Continues a

reference :: b -> (a -> b) -> Reference a -> b
reference b f Starts = b
reference b f (Continues a) = f a

instance IsString a => IsString (Reference a) where
  fromString "" = Starts
  fromString s = Continues (fromString s)

instance Field_ a => Field_ (Reference a) where
    type Compound (Reference a) = Compound a
    m #. k = Continues (m #. k)
    
newtype SetChain =
  SetChain {
    getChain
      :: forall a .
          Binding
            Components
            (Nested Components a)
            (Visibility (Nested Components a))
    }

instance IsString SetChain where
  fromString s =
    SetChain
      (Right . Local <$> sendBinding (singleton (fromString s)))

instance Field_ SetChain where
  type
    Compound SetChain = Reference SetChain
  
  Starts #. n =
    SetChain (fmap (Left . Public) (sendBinding (singleton n)))
  Continues (SetChain b) #. n =
    SetChain (lmap (wrapPaths . singleton n) b)
      
newtype SetPath =
  SetPath {
    getPath
      :: forall a .
          Binding Components a (Visibility (Nested Components a))
    }

setPath :: SetChain -> SetPath
setPath (SetChain b) = SetPath (lmap Leaf b)

instance IsString SetPath where
  fromString s = setPath (fromString s)
        
instance Field_ SetPath where
  type Compound SetPath = Reference SetChain
  p #. n = setPath (p #. n)


-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun
  :: Let_ s => Pun (Lhs s) (Rhs s) -> s
pun (Pun p a) = p #= a

instance (IsString p, IsString a) => IsString (Pun p a) where
  fromString n = Pun (fromString n) (fromString n)

instance (Field_ p, Field_ a) => Field_ (Pun p a) where
  type Compound (Pun p a) = Pun (Compound p) (Compound a)
  Pun p a #. n = Pun (p #. n) (a #. n)


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
  traverse f m = runC m (\ r k -> fmap sendC (traverse (f . k) r))

instance Align r => Align (C r) where
  nil = C (\ kf -> kf nil absurd)
  
  alignWith f ma mb = C (\ kf ->
    runC ma (\ ra ka ->
    runC mb (\ rb kb ->
      kf (align ra rb) (f . bimap ka kb))))
