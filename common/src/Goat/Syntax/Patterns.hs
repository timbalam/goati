{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables, EmptyCase #-}
-- | Intermediate builders for path and pattern syntax
module Goat.Syntax.Patterns
  where

--import Goat.Comp (run)
import qualified Goat.Syntax.Class as S
import qualified Goat.Syntax.Syntax as P
--import Goat.Lang.Field (SomePath, fromPath)
--import Goat.Lang.Let (SomeMatch, fromMatch)
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

instance S.IsString (Path k) where
  fromString s = Path (S.fromString s) id

instance S.IsString k => S.Field_ (Path k) where
  type Compound (Path k) = Path k
  Path n f #. n' = Path n (f
    . Node . wrap
    . M.singleton (S.ident S.fromString n')
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
  :: (S.IsString k, Ord k) => [(Path k, a)] -> Comps k (Node k a)
compsFromList = foldMap (\ (Path n f, a) ->
  (Comps
    . M.singleton (S.ident S.fromString n)
    . f
    . Node)
    (pure a))
  
importsFromList
  :: [(P.Ident, a)] -> Comps P.Ident [a]
importsFromList = foldMap (\ (n, a) ->
  (Comps . M.singleton n) (pure a))
  
   
-- | A set of components partitioned by top-level visibility.
data Vis k a =
  Vis { private :: M.Map S.Ident a, public :: M.Map k a }
  deriving (Functor, Foldable, Traversable)
  
instance (Ord k, Monoid a) => Monoid (Vis k a) where
  mempty = Vis{private=M.empty,public=M.empty}
  Vis{private=l1,public=s1} `mappend` Vis{private=l2,public=s2} =
    Vis{private=(M.unionWith mappend l1 l2),public=(M.unionWith mappend s1 s2)}
  
introVis
  :: (S.IsString k, Ord k)
  => a
  -> P.Vis (Path k) (Path k)
  -> Vis k (Node k a)
introVis a (P.Pub (Path n f)) = Vis
  { private = M.empty
  , public =
      (M.singleton (S.ident S.fromString n) . f . Node) (pure a)
  }
introVis a (P.Priv (Path n f)) = Vis
  { private = (M.singleton n . f . Node) (pure a)
  , public = M.empty
  }

visFromList
  :: (S.IsString k, Ord k)
  => [(P.Vis (Path k) (Path k), a)]
  -> Vis k (Node k a)
visFromList = foldMap (\ (s, mb) -> introVis mb s)
  
  
-- | Enumerate a set of declared public names
newtype Names_ s = Names_ ([String], s)
  deriving (Functor, Applicative)
  
-- | Block statement with destructing pattern assignments. 
newtype Stmt w a = Stmt (w, Maybe a)

decl :: s -> Stmt [s] a
decl s = Stmt ([s], Nothing)
  
  
instance S.IsString s => S.IsString (Stmt [s] a) where
  fromString n = decl (S.fromString n)
{-
instance
  S.IsString s => S.IsString (Rel (Names_ (Stmt [s] a)))
  where
    fromString "" = Self
    fromString n = Rel (Names_ ([n], S.fromString n))
-}
  
instance S.Field s => S.Field_ (Stmt [s] a) where
  type Compound (Stmt [s] a) = S.Compound s
  p #. n = decl (p S.#. n)
{-
instance
  (S.Field s, S.IsString (S.Compound s))
   => S.Field_ (Rel (Names_ (Stmt [s] a)))
  where
    type Compound (Rel (Names_ (Stmt [s] a))) =
      Rel (Names_ (S.Compound s))
    Self #. n = Rel (Names_ ([n], S.fromString "" #. n))
    Rel p #. n = Rel p <&> (S.#. n)
-}

instance Traversable f => S.Let_ (Stmt [s] (f Bind, a)) where
  type Lhs (Stmt [s] (f Bind, a)) = f (Maybe s)
  type Rhs (Stmt [s] (f Bind, a)) = a
  p #= a = Stmt (traverse 
    (maybe ([], Skip) (\ s -> ([s], Bind)))
    p <&> (\ p' -> Just (p', a)))
{-
instance Traversable f => S.Let_ (Names_ (Stmt [s] (f Bind, a))) where
  type Lhs (Names_ (Stmt [s] (f Bind, a))) = Names_ (f (Maybe s))
  type Rhs (Names_ (Stmt [s] (f Bind, a))) = a
  p #= a = p <&> (S.#= a)
-}
    
{-
instance (Traversable f, S.Esc_ a)
 => S.Esc_ (Stmt [s] (f Bind, a)) where
  type Lower (Stmt [s] (f Bind, a)) =
    Pun (f (Maybe s)) (S.Lower a)
  esc_ = pun
instance (Traversable f, S.Esc_ a)
 => S.Esc_ (Names_ (Stmt [s] (f Bind, a))) where
  type Lower (Names_ (Stmt [s] (f Bind, a))) =
    Pun (Names_ (f (Maybe s))) (S.Lower a)
  esc_ = pun
-}


-- | A leaf pattern that can bind the matched value or skip
data Bind = Bind | Skip
  deriving (Eq, Show)

bind :: a -> a -> Bind -> a
bind a _ Bind = a
bind _ a Skip = a


buildVis
  :: (S.IsString k, Ord k)
  => [Stmt [P.Vis (Path k) (Path k)] a]
  -> (Vis k (Node k (Maybe Int)), [a])
buildVis rs = (visFromList kvs, as) where
  as = mapMaybe (\ (Stmt (_, mb)) -> mb) rs
  kvs = enumJust rs
  

buildComps
  :: (S.IsString k, Ord k)
  => [Stmt [Path k] a]
  -> (Comps k (Node k (Maybe Int)), [a])
buildComps rs = (compsFromList kvs, as) where
  as = mapMaybe (\ (Stmt (_, mb)) -> mb) rs
  kvs = enumJust rs
  
  
buildImports
 :: [Stmt [P.Ident] a]
 -> (Comps P.Ident [Maybe Int], [a])
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

instance S.Esc_ (Esc a) where
  type Lower (Esc a) = a
  esc_ = Esc  


-- | A tree of path matches
newtype Matching k a =
  Matching { getMatching :: M.Map k (Node k a) }
{-
instance S.Esc_ (Matching k a) where 
  type Lower (Matching k a) = Pun (Path k) a
  esc_ = pun
-}

matchPun
 :: S.IsString k
 => Pun (P.Vis (Path k) (Path k)) a -> Matching k a
matchPun (Pun p a) = P.Pub (P.vis id id p) S.#= a

instance
  (S.IsString k, S.IsString a) => S.IsString (Matching k a)
  where
    fromString s = matchPun (S.fromString s)

instance
  (S.IsString k, S.Field_ a) => S.Field_ (Matching k a) 
  where
    type Compound (Matching k a) =
      Pun (Maybe (P.Vis (Path k) (Path k))) (S.Compound a)
    c #. i = matchPun (c S.#. i)

instance S.IsString k => S.Let_ (Matching k a) where
  type Lhs (Matching k a) = P.Vis (Path k) P.NoPriv
  type Rhs (Matching k a) = a
  P.Pub (Path n f) #= a =
    (Matching
      . M.singleton (S.ident S.fromString n)
      . f
      . Node)
      (pure a)
  P.Priv x #= _ = case x of {}

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun
  :: S.Let_ s => Pun (S.Lhs s) (S.Rhs s) -> s
pun (Pun p a) = p S.#= a

instance (S.IsString p, S.IsString a) => S.IsString (Pun p a) where
  fromString n = Pun (S.fromString n) (S.fromString n)

instance (S.Field p, S.Field a) => S.Field_ (Pun p a) where
  type Compound (Pun p a) = Pun (S.Compound p) (S.Compound a)
  Pun p a #. n = Pun (p S.#. n) (a S.#. n)

  
-- | Plain path
newtype Plain a = Plain a
  deriving (Functor, Foldable, Traversable)
  
instance S.IsString a => S.IsString (Plain (Maybe a)) where
  fromString s = Plain (Just (S.fromString s))
{-
instance
  S.IsString a => S.IsString (Rel (Names_ (Plain (Maybe a))))
  where
    fromString "" = Self
    fromString n = Rel (Names_ ([n], S.fromString n))
-}
  
instance S.Field a => S.Field_ (Plain (Maybe a)) where
  type Compound (Plain (Maybe a)) = S.Compound a
  a #. n = Plain (Just (a S.#. n))
{-
instance
  S.Field a => S.Field_ (Rel (Names_ (Plain (Maybe a))))
  where
    type Compound (Names_ (Plain (Maybe a))) =
      Rel (Names_ (S.Compound a))
    Self #. n = Rel (Names_ ([n], S.fromString "" S.#. n))
    Rel a #. n = Rel (a <&> (S.#. n))
-}
  

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
  
instance S.IsString a => S.IsString (Patt f (Maybe a)) where
  fromString n = letpath (S.fromString n)
{-
instance
  S.IsString a => S.IsString (Rel (Names_ (Patt f (Maybe a))))
  where
    fromString "" = Self
    fromString n = Rel (Names_ ([n], S.fromString n))
-}
  
instance S.Field a => S.Field_ (Patt f (Maybe a)) where
  type Compound (Patt f (Maybe a)) = S.Compound a
  p #. n = letpath (p S.#. n)
{-
instance
  S.Field a => S.Field_ (Rel (Names_ (Patt f (Maybe a))))
  where
    type Compound (Rel (Names_ (Patt f (Maybe a)))) =
      Rel (Names_ (S.Compound a))
    Self #. n = Rel (Names_ ([n], S.fromString "" S.#. n))
    Rel p #. n = Rel (p <&> (S.#. n))
-}

instance
  (S.IsString k, Ord k, S.Path a)
   => S.Block_ (Patt (Matches k) (Maybe a)) where
  type Stmt (Patt (Matches k) (Maybe a)) =
    Matching k (Patt (Matches k) (Maybe a))
  block_ ts = Nothing :< S.block_ ts
{-
instance (S.IsString k, Ord k, S.Path a)
 => S.Block_ (Names_ (Patt (Matches k) (Maybe a))) where
  type Stmt (Names_ (Patt (Matches k) (Maybe a))) =
    Matching k (Names_ (Patt (Matches k) (Maybe a)))
  block_ ts = (Nothing :<) <$> S.block_ ts
-}
  
instance
  (S.IsString k, Ord k, S.Path a)
   => S.Block_ (Decomp (Matches k) a) where
  type Stmt (Decomp (Matches k) a) = Matching k a
  block_ ts = Decomp [c] where
    c = Compose (foldMap (Comps . getMatching) ts)
{-
instance (S.IsString k, Ord k, S.Path a)
 => S.Block_ (Names_ (Decomp (Matches k) a)) where
  type Stmt (Names_ (Decomp (Matches k) a)) =
    Matching k (Names_ a)
  block_ ts = Decomp . pure <$> c where
    c = sequenceA (Compose (foldMap (Comps . getMatching) ts))
-}
  
instance S.Extend_ (Patt f a) where
  type Extension (Patt f a) = Decomp f (Patt f a)
  type Ext (Patt f a) = Patt f a 
  (a :< Decomp ns) # Decomp ns' = a :< Decomp (ns' ++ ns)
{-
instance S.Extend_ (Names_ (Patt f a)) where
  type Ext (Names_ (Patt f a)) = Names_ (Decomp f (Patt f a))
  (#) = liftA2 (S.#)
-}
{-
matchesProof
 :: (S.IsString k, Ord k, S.Path a)
 => SomeMatch -> Matching k (Patt (Matches k) (Maybe a))
matchesProof = run . fromMatch
-}
  