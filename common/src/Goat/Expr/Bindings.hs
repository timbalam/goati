{-# LANGUAGE TypeFamilies, FlexibleInstances, ExistentialQuantification, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveTraversable, RankNTypes #-}
module Goat.Expr.Bindings
  where

import Goat.Lang.Ident (Ident, IsString(..))
import Goat.Lang.Let (Let_(..))
import Goat.Lang.Field (Field_(..))
import Goat.Util (Compose(..))
import Control.Monad (ap, liftM, join)
--import Control.Monad.Free
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Profunctor
import qualified Data.Map as Map
import Data.Align (Align(..), bicrosswalk)
import Data.Semigroup
import Data.These (These(..), these, mergeTheseWith, mergeThese)
import Data.Void (absurd)

--infixl 5 :?

newtype Components a = Components (Map.Map Ident a)
  deriving (Align, Functor, Foldable, Traversable)

csingleton :: Ident -> a -> Components a
csingleton k a = Components (Map.singleton k a)

cempty :: Components a
cempty = Components Map.empty

-- | A possibly ambiguous value with two states,
-- a leaf / final type 'b' and
-- an node / extensible nested type 'r'.
data Grouped r a =
    forall x . Node (r x) (x -> Grouped r a)
  | Leaf a
  | forall x . NodeAndLeaf (r x) (x -> Grouped r a) a

sendGrouped :: r a -> Grouped r a
sendGrouped r = Node r Leaf

wrapGrouped :: r (Grouped r a) -> Grouped r a
wrapGrouped r = Node r id

instance Functor (Grouped r) where
  fmap f (Node r k) = Node r (fmap f . k)
  fmap f (Leaf a) = Leaf (f a)
  fmap f (NodeAndLeaf r k a) = NodeAndLeaf r (fmap f . k) (f a)

instance Align r => Align (Grouped r) where
  nil = Node nil absurd
  
  align = align' where
    alignNodes
     :: Align r 
     => r x -> (x -> Grouped r a)
     -> r y -> (y -> Grouped r b)
     -> (forall xx . r xx -> (xx -> Grouped r (These a b)) -> p)
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

instance Foldable r => Foldable (Grouped r) where
  foldMap f (Node r k) = foldMap (foldMap f . k) r
  foldMap f (Leaf a) = f a
  foldMap f (NodeAndLeaf r k a) =
    foldMap (foldMap f . k) r `mappend` f a

instance Traversable r => Traversable (Grouped r) where
  traverse f = traverse' where
    traverseNode
      :: (Traversable r, Applicative f)
      => (a -> f b)
      -> r x -> (x -> Grouped r a)
      -> (forall xx . r xx -> (xx -> Grouped r b) -> p)
      -> f p
    traverseNode f r k g =
      g <$> traverse (traverse f . k) r <*> pure id
    
    traverse' (Node r k)          =
      traverseNode f r k Node
    traverse' (Leaf a)              =
      fmap Leaf (f a)
    traverse' (NodeAndLeaf r k a) =
      traverseNode f r k NodeAndLeaf <*> f a

instance (Align r, Semigroup a) => Semigroup (Grouped r a) where
  a <> b = alignWith (mergeThese (<>)) a b
  
  
-- | LHS bindings
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Foldable, Traversable, Semigroup)

newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable, Semigroup)
  
newtype Visible p a =
  Visible (Map.Map Ident (p (Public a) (Local a)))

vempty :: Visible p a
vempty = Visible Map.empty

vsingleton
 :: Ident -> Either (Public a) (Local a) -> Visible Either a
vsingleton k v = Visible (Map.singleton k v)

instance Bifunctor p => Functor (Visible p) where
  fmap f (Visible kv) =
    Visible (fmap (bimap (fmap f) (fmap f)) kv)

instance Bifoldable p => Foldable (Visible p) where
  foldMap f (Visible kv) =
    foldMap (bifoldMap (foldMap f) (foldMap f)) kv

instance
  Bitraversable p => Traversable (Visible p)
  where
    traverse f (Visible kv) =
      Visible <$> 
        traverse (bitraverse (traverse f) (traverse f)) kv

instance Align (Visible These) where
  nil = vempty
  
  alignWith f (Visible kva) (Visible kvb) =
    Visible (alignWith merge' kva kvb)
    where
      merge' =
        these
          (bimap (fmap (f . This)) (fmap (f . This)))
          (bimap (fmap (f . That)) (fmap (f . That)))
          (align' f)

      align' 
       :: (These a b -> c)
       -> These (Public a) (Local a)
       -> These (Public b) (Local b)
       -> These (Public c) (Local c)
      align' f (This (Public a)) (This (Public b)) =
        This (Public (f (These a b)))
      align' f (That (Local a)) (This (Public b)) =
        These (Public (f (That b))) (Local (f (This a)))
      align' f (These (Public a1) (Local a2)) (This (Public b)) =
        These (Public (f (These a1 b))) (Local (f (This a2)))
      align' f (This (Public a)) (That (Local b)) =
        These (Public (f (This a))) (Local (f (That b)))
      align' f (That (Local a)) (That (Local b)) =
        That (Local (f (These a b)))
      align' f (These (Public a1) (Local a2)) (That (Local b)) =
        These (Public (f (This a1))) (Local (f (These a2 b)))
      align' f (This (Public a)) (These (Public b1) (Local b2)) =
        These (Public (f (These a b1))) (Local (f (That b2)))
      align' f (That (Local a)) (These (Public b1) (Local b2)) =
        These (Public (f (That b1))) (Local (f (These a b2)))
      align'
        f
        (These (Public a1) (Local a2))
        (These (Public b1) (Local b2)) =
        These (Public (f (These a1 b1))) (Local (f (These a2 b2)))

-- | Binding 
data Relative a = Self | Parent a

reference :: b -> (a -> b) -> Relative a -> b
reference b f Self = b
reference b f (Parent a) = f a

instance IsString a => IsString (Relative a) where
  fromString "" = Self
  fromString s = Parent (fromString s)

instance Field_ a => Field_ (Relative a) where
    type Compound (Relative a) = Compound a
    m #. k = Parent (m #. k)
    
newtype SetChain =
  SetChain {
    getChain
      :: forall a .
          Set
            (Visible Either)
            (Grouped Components a)
            (Grouped Components a)
    }

instance IsString SetChain where
  fromString s =
    SetChain
      (Set (vsingleton (fromString s) . Right . Local))

instance Field_ SetChain where
  type
    Compound SetChain = Relative SetChain
  
  Self #. n =
    SetChain
      (Set (vsingleton n . Left . Public))
  Parent (SetChain f) #. n =
    SetChain (lmap (wrapGrouped . csingleton n) f)
      
newtype SetPath =
  SetPath {
    getPath
     :: forall a .
          Set (Visible Either) a (Grouped Components a)
    }

setPath :: SetChain -> SetPath
setPath (SetChain f) = SetPath (lmap Leaf f)

instance IsString SetPath where
  fromString s = setPath (fromString s)
        
instance Field_ SetPath where
  type Compound SetPath = Relative SetChain
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
newtype Set r a b = Set (a -> r b)
  deriving Functor

instance Functor r => Profunctor (Set r) where
  dimap f g (Set h) = Set (fmap g . h . f)

instance Align r => Align (Set r a) where
  nil = Set (const nil)
  
  alignWith f (Set ka) (Set kb) =
    Set (\ a -> alignWith f (ka a) (kb a))


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
