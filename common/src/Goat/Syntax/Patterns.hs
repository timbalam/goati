{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}
-- | Intermediate builders for path and pattern syntax
module Goat.Syntax.Patterns
  where
  
import qualified Goat.Syntax.Class as S
import qualified Goat.Syntax.Syntax as P
import Goat.Util (Compose(..), (<&>), showsUnaryWith)
import Control.Applicative (liftA2)
import Control.Monad.Trans.Free
import Control.Monad.State
import Control.Comonad.Cofree
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce
--import Data.List (nub)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Prelude.Extras
  
  
-- | Builder for a path
data Path k = Path S.Ident (forall a. (Node k a -> Node k a))

instance S.Self (Path k) where self_ n = Path n id
instance S.Local (Path k) where local_ n = Path n id
  
instance S.Self k => S.Field_ (Path k) where
  type Compound (Path k) = Path k
  Path n f #. n' = Path n (f . Node . wrap
    . M.singleton (S.self_ n')
    . getNode)
  
  
-- | A tree of paths
newtype Node k a = Node { getNode :: FreeT (M.Map k) ((,) [a]) a }
  
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
        
     
-- | Set of components
newtype Comps k a = Comps { getComps :: M.Map k a }
  deriving (Functor, Foldable, Traversable)
  
instance (Ord k, Monoid a) => Monoid (Comps k a) where
  mempty = Comps M.empty
  Comps m1 `mappend` Comps m2 = Comps (M.unionWith mappend m1 m2)
  
compsFromList
  :: (S.Self k, Ord k) => [(Path k, a)] -> Comps k (Node k a)
compsFromList = foldMap (\ (Path n f, a) ->
  (Comps . M.singleton (S.self_ n) . f . Node) (pure a))
  
importsFromList
  :: (S.Extern k, Ord k) => [(S.Ident, a)] -> Comps k [a]
importsFromList = foldMap (\ (n, a) ->
  (Comps . M.singleton (S.use_ n)) (pure a))
  
   
-- | A set of components partitioned by top-level visibility.
data Vis k a = Vis { private :: M.Map S.Ident a, public :: M.Map k a }
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
  
  
-- | Enumerate a set of declared public names
newtype Names s = Names ([S.Ident], s)
  deriving (Functor, Applicative)
  
-- | Block statement with destructing pattern assignments. 
newtype Stmt w a = Stmt (w, Maybe a)

decl :: s -> Stmt [s] a
decl s = Stmt ([s], Nothing)
  
  
instance S.Self s => S.Self (Stmt [s] a) where
  self_ n = decl (S.self_ n)
instance S.Self s => S.Self (Names (Stmt [s] a)) where
  self_ n = Names ([n], S.self_ n) 
  
instance S.Field s => S.Field_ (Stmt [s] a) where
  type Compound (Stmt [s] a) = S.Compound s
  p #. n = decl (p S.#. n)
instance S.Field s => S.Field_ (Names (Stmt [s] a)) where
  type Compound (Names (Stmt [s] a)) = Names (S.Compound s)
  p #. n = p <&> (S.#. n)

instance Traversable f => S.Let_ (Stmt [s] (f Bind, a)) where
  type Lhs (Stmt [s] (f Bind, a)) = f (Maybe s)
  type Rhs (Stmt [s] (f Bind, a)) = a
  p #= a = Stmt (traverse 
    (maybe ([], Skip) (\ s -> ([s], Bind)))
    p <&> (\ p' -> Just (p', a)))
instance Traversable f => S.Let_ (Names (Stmt [s] (f Bind, a))) where
  type Lhs (Names (Stmt [s] (f Bind, a))) = Names (f (Maybe s))
  type Rhs (Names (Stmt [s] (f Bind, a))) = a
  p #= a = p <&> (S.#= a)
    
instance (Traversable f, S.Esc a)
 => S.Esc (Stmt [s] (f Bind, a)) where
  type Lower (Stmt [s] (f Bind, a)) =
    Pun (f (Maybe s)) (S.Lower a)
  esc_ = pun
instance (Traversable f, S.Esc a)
 => S.Esc (Names (Stmt [s] (f Bind, a))) where
  type Lower (Names (Stmt [s] (f Bind, a))) =
    Pun (Names (f (Maybe s))) (S.Lower a)
  esc_ = pun


-- | A leaf pattern that can bind the matched value or skip
data Bind = Bind | Skip
  deriving (Eq, Show)

bind :: a -> a -> Bind -> a
bind a _ Bind = a
bind _ a Skip = a


buildVis
  :: forall k a. (S.Self k, Ord k)
  => [Stmt [P.Vis (Path k) (Path k)] a]
  -> (Vis k (Node k (Maybe Int)), [a])
buildVis rs = (visFromList kvs, as) where
  as = mapMaybe (\ (Stmt (_, mb)) -> mb) rs
  kvs = enumJust rs
  

buildComps
  :: forall k a. (S.Self k, Ord k)
  => [Stmt [Path k] a]
  -> (Comps k (Node k (Maybe Int)), [a])
buildComps rs = (compsFromList kvs, as) where
  as = mapMaybe (\ (Stmt (_, mb)) -> mb) rs
  kvs = enumJust rs
  
  
buildImports
 :: forall k a. (S.Extern k, Ord k)
 => [Stmt [S.Ident] a]
 -> (Comps k [Maybe Int], [a])
buildImports rs = (importsFromList kvs, as) where
  as = mapMaybe (\ (Stmt (_, mb)) -> mb) rs
  kvs = enumJust rs
  
  
enumJust :: forall a b . [Stmt [a] b] -> [(a, Maybe Int)]
enumJust cs = concat (evalState (traverse enumPair cs) 0) where
  
  enumPair (Stmt (xs, Just _ )) = 
    traverse (\ a -> state (\ i -> ((a, Just i), i+1))) xs
  enumPair (Stmt (xs, Nothing)) = pure (map (flip (,) Nothing) xs)


matched
  :: Applicative f => [f [b]] -> f [b]
matched fs = concat <$> sequenceA fs

-- | Wrapper for a pattern that binds outside the enclosing decomp block
newtype Esc a = Esc { getEsc :: a }

instance S.Esc (Esc a) where
  type Lower (Esc a) = a
  esc_ = Esc  


-- | A tree of path matches
newtype Matching k a = Matching { getMatching :: M.Map k (Node k a) }

instance S.Self k => S.Esc (Matching k a) where 
  type Lower (Matching k a) = Pun (Path k) a
  esc_ = pun

instance S.Self k => S.Let_ (Matching k a) where
  type Lhs (Matching k a) = Path k
  type Rhs (Matching k a) = Esc a
  Path n f #= Esc a =
    (Matching . M.singleton (S.self_ n) . f . Node) (pure a)


-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun
  :: (S.Let_ s, S.Esc (S.Rhs s))
  => Pun (S.Lhs s) (S.Lower (S.Rhs s)) -> s
pun (Pun p a) = p S.#= S.esc_ a

instance (S.Self p, S.Self a) => S.Self (Pun p a) where self_ n = Pun (S.self_ n) (S.self_ n)
instance (S.Self p, S.Local a) => S.Local (Pun p a) where
  local_ n = Pun (S.self_ n) (S.local_ n)

instance (S.Field p, S.Field a) => S.Field_ (Pun p a) where
  type Compound (Pun p a) = Pun (S.Compound p) (S.Compound a)
  Pun p a #. n = Pun (p S.#. n) (a S.#. n)

  
-- | Plain path
newtype Plain a = Plain a
  deriving (Functor, Foldable, Traversable)
  
instance S.IsString a => S.IsString (Plain (Maybe a)) where
  fromString s = Plain (Just (S.fromString s))

instance S.Self a => S.Self (Plain (Maybe a)) where
  self_ n = Plain (Just (S.self_ n))
instance S.Self a => S.Self (Names (Plain (Maybe a))) where
  self_ n = Names ([n], S.self_ n)
  
instance S.Local a => S.Local (Plain (Maybe a)) where
  local_ n = Plain (Just (S.local_ n))
instance S.Local a => S.Local (Names (Plain (Maybe a))) where
  local_ n = pure (S.local_ n)
  
instance S.Field a => S.Field_ (Plain (Maybe a)) where
  type Compound (Plain (Maybe a)) = S.Compound a
  a #. n = Plain (Just (a S.#. n))
instance S.Field a => S.Field_ (Names (Plain (Maybe a))) where
  type Compound (Names (Plain (Maybe a))) = Names (S.Compound a)
  a #. n = a <&> (S.#. n)
  

-- | Pattern
type Patt f = Cofree (Decomp f)
newtype Decomp f a = Decomp { getDecomp :: [f a] }
  deriving (Functor, Foldable, Traversable)
  
instance Eq1 f => Eq1 (Decomp f) where
  Decomp fs ==# Decomp fs' = fmap Lift1 fs == fmap Lift1 fs'
  
instance (Eq1 f, Eq a) => Eq (Decomp f a) where
  (==) = (==#)
  
instance Show1 f => Show1 (Decomp f) where
  showsPrec1 d (Decomp fs) =
    showsUnaryWith showsPrec "Decomp" d (fmap Lift1 fs)
  
instance (Show1 f, Show a) => Show (Decomp f a) where
  showsPrec = showsPrec1

  
type Matches k = Compose (Comps k) (Node k)
  
letpath :: a -> Patt f (Maybe a)
letpath a = Just a :< Decomp []
  
instance S.Self a => S.Self (Patt f (Maybe a)) where
  self_ n = letpath (S.self_ n)
instance S.Self a => S.Self (Names (Patt f (Maybe a))) where
  self_ n = Names ([n], S.self_ n)

instance S.Local a => S.Local (Patt f (Maybe a)) where
  local_ n = letpath (S.local_ n)
instance S.Local a => S.Local (Names (Patt f (Maybe a))) where
  local_ n = pure (S.local_ n)
  
instance S.Field a => S.Field_ (Patt f (Maybe a)) where
  type Compound (Patt f (Maybe a)) = S.Compound a
  p #. n = letpath (p S.#. n)
instance S.Field a => S.Field_ (Names (Patt f (Maybe a))) where
  type Compound (Names (Patt f (Maybe a))) = Names (S.Compound a)
  p #. n = p <&> (S.#. n)

instance (S.Self k, Ord k, S.RelPath a, S.LocalPath a)
 => S.Block_ (Patt (Matches k) (Maybe a)) where
  type Stmt (Patt (Matches k) (Maybe a)) =
    Matching k (Patt (Matches k) (Maybe a))
  block_ ts = Nothing :< S.block_ ts
instance (S.Self k, Ord k, S.RelPath a, S.LocalPath a)
 => S.Block_ (Names (Patt (Matches k) (Maybe a))) where
  type Stmt (Names (Patt (Matches k) (Maybe a))) =
    Matching k (Names (Patt (Matches k) (Maybe a)))
  block_ ts = (Nothing :<) <$> S.block_ ts
  
instance (S.Self k, Ord k, S.RelPath a, S.LocalPath a)
 => S.Block_ (Decomp (Matches k) a) where
  type Stmt (Decomp (Matches k) a) = Matching k a
  block_ ts = Decomp [c] where
    c = Compose (foldMap (Comps . getMatching) ts)
instance (S.Self k, Ord k, S.RelPath a, S.LocalPath a)
 => S.Block_ (Names (Decomp (Matches k) a)) where
  type Stmt (Names (Decomp (Matches k) a)) = Matching k (Names a)
  block_ ts = Decomp . pure <$> c where
    c = sequenceA (Compose (foldMap (Comps . getMatching) ts))
  
instance S.Extend_ (Patt f a) where
  type Ext (Patt f a) = Decomp f (Patt f a)
  (a :< Decomp ns) # Decomp ns' = a :< Decomp (ns' ++ ns)
instance S.Extend_ (Names (Patt f a)) where
  type Ext (Names (Patt f a)) = Names (Decomp f (Patt f a))
  (#) = liftA2 (S.#)
  