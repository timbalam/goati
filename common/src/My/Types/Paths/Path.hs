module My.Types.Paths.Path
  where
  
import qualified My.Types.Syntax.Class as S
import qualified My.Types.Syntax as P
import Control.Monad.Trans.Free
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
  
  
-- | Builder for a path
data Path p = Path S.Ident (p -> p)
    --(forall m a. MonadFree ((,) S.Ident) m => m a -> m a)

instance S.Self (Path p) where self_ n = Path n id
instance S.Local (Path p) where local_ n = Path n id
  
instance (Monoid w, S.Self k) => S.Field (Path (Node k w a)) where
  type Compound (Path (Node k w a)) = Path (Node k w a)
  Path n f #. n' = Path n (f . Node . wrap . M.singleton n' . getNode)
  
  
-- | Thread a writer through levels of a tree of paths
newtype Node k w a = Node { getNode ::
  FreeT (M.Map k) ((,) w) a }
  deriving (Functor, Foldable, Traversable, Applicative, Monad)
  
instance Bifunctor (Node k) where
  bimap f g (Node (FreeT p)) =
    (Node . FreeT)
      (bimap f (bimap g (getNode . bimap f g . Node)) p)
    
instance Bifoldable (Node k) where
  bifoldMap f g (Node (FreeT p)) =
    bifoldMap f (bifoldMap g (bifoldMap f g . Node)) p
    
instance Bitraversable (Node k) where
  bitraverse f g (Node (FreeT p)) =
    Node . FreeT <$>
      (bitraverse f . bitraverse g) (fmap getNode
        . bitraverse f g . Node) p

instance Ord k => Monoid (Node k [a] a) where
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
newtype Comps k a = Comps (M.Map k (Node k [a] a))

instance Functor (Comps k) where
  fmap f (Comps kv) = Comps (fmap (bimap (fmap f) f) kv)
  
instance Foldable (Comps k) where
  foldMap f (Comps kv) = foldMap (bifoldMap (foldMap f) f) kv
  
instance Traversable (Comps k) where
  traverse f (Comps kv) =
    fmap Comps (traverse (bitraverse (traverse f) f) kv)
  
instance Ord k => Monoid (Comps k a) where
  mempty = Comps M.empty
  Comps m1 `mappend` Comps m2 = Comps (M.unionWith mappend m1 m2)
  
   
-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value,
-- indicating that the path is to be checked for ambiguity but not assigned a value.
data Vis k a = Vis { private :: M.Map S.Ident a, public :: M.Map k a }
  deriving (Functor, Foldable)
  
introVis
  :: (S.Self k, Applicative f)
  => a -> P.Vis (Path (f a)) (Path (f a)) -> Vis k (f a)
introVis a (P.Pub (Path n f)) =
  Vis{private=M.empty,public=(M.singleton (S.self_ n) (f (pure a)))}
introVis a (P.Priv (Path n f)) =
  Vis{private=(M.singleton n (f (pure a))),public=M.empty}

instance (Ord k, Monoid a) => Monoid (Vis k a) where
  mempty = Vis{private=M.empty,public=M.empty}
  Vis{private=l1,public=s1} `mappend` Vis{private=l2,public=s2} =
    Vis{private=(M.unionWith mappend l1 l2),public=(M.unionWith mappend s1 s2)}
    
visFromList
  :: (S.Self k, Applicative f)
  => [(P.Vis (Path (f a)) (Path (f a)), Maybe a)] -> Vis k (f a)
visFromList = foldMap (\ (s, mb) -> introVis mb s)

  