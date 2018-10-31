{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
-- | Path syntax intermediate builder
module Goat.Types.Paths.Path
  where
  
import qualified Goat.Syntax.Class as S
import qualified Goat.Syntax.Syntax as P
import Control.Applicative (liftA2)
import Control.Monad.Trans.Free
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import qualified Data.Map as M
  
  
-- | Builder for a path
data Path k = Path S.Ident
  (forall a. (Node k a -> Node k a))

instance S.Self (Path k) where self_ n = Path n id
instance S.Local (Path k) where local_ n = Path n id
  
instance S.Self k => S.Field (Path k) where
  type Compound (Path k) = Path k
  Path n f #. n' = Path n (f . Node . wrap
    . M.singleton (S.self_ n')
    . getNode)
  
  
-- | Thread a writer through levels of a tree of paths
newtype Node k a = Node { getNode ::
  FreeT (M.Map k) ((,) [a]) a }
  
instance Functor (Node k) where
  fmap f (Node m) = Node (go m) where
    go (FreeT p) =
      FreeT 
        (bimap
          (fmap f)
          (bimap f go)
          p)
    
instance Foldable (Node k) where
  foldMap f (Node m) = go m where
    go (FreeT p) =
      bifoldMap
        (foldMap f)
        (bifoldMap f go)
        p
    
instance Traversable (Node k) where
  traverse f (Node m) = fmap Node (go m) where
    go (FreeT p) =
      fmap FreeT
        (bitraverse
          (traverse f)
          (bitraverse f go)
          p)

instance Ord k => Monoid (Node k a) where
  mempty = Node (liftF M.empty)
  
  Node m1 `mappend` Node m2 = Node (mappend' m1 m2) where
    mappend' (FreeT (as1, Pure a1 )) (FreeT (as2, ff2     )) =
      FreeT ([a1] ++ as1 ++ as2, ff2    )
    mappend' (FreeT (as1, ff1     )) (FreeT (as2, Pure a2 )) =
      FreeT (as1 ++ [a2] ++ as2, ff1    )
    mappend' (FreeT (as1, Free kv1)) (FreeT (as2, Free kv2)) =
      FreeT (as1 ++ as2        , Free kv')
      where
        kv' = M.unionWith mappend' kv1 kv2
        
     
-- | Tree of components
newtype Comps k a = Comps { getComps :: M.Map k a }
  deriving (Functor, Foldable, Traversable)
  
instance (Ord k, Monoid a) => Monoid (Comps k a) where
  mempty = Comps M.empty
  Comps m1 `mappend` Comps m2 = Comps (M.unionWith mappend m1 m2)
  
   
-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value,
-- indicating that the path is to be checked for ambiguity but not assigned a value.
data Vis k a = Vis
  { private :: M.Map S.Ident a
  , public :: M.Map k a
  }
  deriving (Functor, Foldable, Traversable)
  
instance (Ord k, Monoid a) => Monoid (Vis k a) where
  mempty = Vis{private=M.empty,public=M.empty}
  Vis{private=l1,public=s1} `mappend` Vis{private=l2,public=s2} =
    Vis{private=(M.unionWith mappend l1 l2),public=(M.unionWith mappend s1 s2)}
  
introVis
  :: S.Self k
  => a -> P.Vis (Path k) (Path k) -> Vis k (Node k a)
introVis a (P.Pub (Path n f)) = Vis
  { private = M.empty
  , public = (M.singleton (S.self_ n) . f . Node) (pure a)
  }
introVis a (P.Priv (Path n f)) = Vis
  { private = (M.singleton n . f . Node) (pure a)
  , public = M.empty
  }
    
visFromList
  :: (S.Self k, Ord k)
  => [(P.Vis (Path k) (Path k), a)]
  -> Vis k (Node k a)
visFromList = foldMap (\ (s, mb) -> introVis mb s)

  