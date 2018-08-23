{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | This module contains functions for abstractly validating sets of definitions made
-- using the syntax classes for duplicated names, overlapping definitions, etc. 
module My.Syntax.Vocabulary
  ( DefnError(..)
  , Defns(..), Paths(..), VisPaths(..)
  , disambigpub, disambigpriv, disambigvis, disambigmatch
  , Path(..), Patt(..), Pun(..)
  , BlockDefns(..), TupDefns(..), MatchDefns(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr (Ident)
import My.Types.Classes (MyError(..))
import qualified My.Types.Syntax.Class as S
import My.Util (Collect(..), collect, (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free.Church (MonadFree(..), F)
import Data.Semigroup
import Data.String (IsString(..))
import Data.Functor.Plus (Plus(..), Alt(..))
import Data.Typeable
import qualified Data.Map as M
--import qualified Data.Set as S


-- | Errors from binding definitions
data DefnError =
    OlappedMatch (P.Path P.Key)
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet P.VarPath
  -- ^ Error if a group assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately in a group
  deriving (Eq, Show, Typeable)
  
instance MyError DefnError where
  displayError (OlappedMatch p) = "Ambiguous destructuring of path " ++ show p
  displayError (OlappedSet p) = "Ambiguous assignment to path " ++ show p
  displayError (OlappedVis i) = "Variable assigned with multiple visibilities " ++ show i
  
  
-- | A 'Path' is a sequence of nested names. We represent as an insert function for
-- nested paths.
data Path = Path (forall a. Amb a -> (Ident, Amb a))

instance S.Self Path where self_ i = Path (i,)
instance S.Local Path where local_ i = Path (i,)
  
instance S.Field Path where
  type Compound Path = Path
  Path f #. i = Path (f . Disjoint . M.singleton i)

    
-- | A set of paths possibly with associated values of type 'a'.
newtype Paths a = Paths { unPaths :: M.Map Ident (Amb (Maybe a)) }
  deriving Functor

-- | 'intro' forms a singleton path group
intro :: Path -> Maybe a -> Paths a
intro (Path f) = Paths . uncurry M.singleton . f . pure

instance Alt Paths where Paths g1 <!> Paths g2 = Paths (M.unionWith (<!>) g1 g2)
instance Plus Paths where zero = Paths M.empty


-- | Validate that a finished tree has unambiguous paths and construct 
-- an expression that reflects the tree of assigned values.
--
-- If there are any ambiguous paths, returns them as list of 'OlappedSet'
-- errors.
--
-- Paths with missing 'Nothing' values represent paths that are validated but
-- not assigned, and unassigned trees of paths are not included in output.
disambigpub, disambigpriv
  :: (Applicative f, S.Path a, S.Extend a, S.Tuple (S.Ext a), S.Member (S.Ext a) ~ Maybe a)
  => Paths (Collect [DefnError] (a -> f a))
  -> Collect [DefnError] (M.Map Ident (a -> f (Maybe a)))
disambigpub = disambig (OlappedSet . P.Pub . fmap P.K_)
disambigpriv = disambig (OlappedSet . P.Priv)

disambig
  :: (S.Path p, S.Path a, S.Extend a, S.Tuple (S.Ext a), S.Member (S.Ext a) ~ Maybe a)
  => (p -> DefnError)
  -> p
  -> Amb (Collect [DefnError] (a -> f (Maybe a)))
  -> Collect [DefnError] (a -> f (Maybe a))
disambig f = go
  where
    go _ (Overlap c Nothing) = c
    go p (Overlap _ (Just b)) = (collect . pure) (f p) *> go p b
    go p (Disjoint m) =
      toExt <$> M.traverseWithKey (\ k a -> go (p #. k) a) m
        
    toExt :: Applicative f => M.Map Ident (a -> f (Maybe a)) -> a -> f (Maybe a)
    toExt m e = Just . (e #) . tup_ <$> x where 
      s = M.foldrWithKey
        (\ k f s -> 
          liftA2 (\ s e -> s #: (S.self_ k #= e)) s (f (e #. k)))
        (pure S.empty)
        m

        
-- | Paths partitioned by top-level visibility
data VisPaths a = VisPaths { local :: Paths a, public :: Paths a }
  deriving Functor

introVis :: P.Vis Path -> Maybe a -> VisPaths a
introVis (P.Priv p) a = zero {local = intro p a}
introVis (P.Pub p) a = zero {public = intro p a}
  
instance Alt VisPaths where
  VisPaths l1 s1 <!> VisPaths l2 s2 = VisPaths (l1 <!> l2) (s1 <!> s2)

instance Plus VisPaths where zero = VisPaths zero zero
    
    
-- | Validate that a group of private/public definitions are disjoint.
disambigvis
  :: (S.Path a, S.Extend a, S.Tuple (S.Ext a), S.Member (S.Ext a) ~ Maybe a)
  => VisPaths (Collect [DefnError] a)
  -> Collect [DefnError] (M.Map Ident (Maybe (a -> a)), M.Map Ident (Maybe (a -> a)))
disambigvis (VisPaths {local=loc, public=pub}) =
  viserrs *> liftA2 (,) (disambigpriv loc) (disambigpub pub)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    viserrs = M.foldrWithKey
      (\ l (a, b) e -> e *> (collect . pure) (OlappedVis l))
      (pure ())
      (M.intersectionWith (,) locn pubn)

    locn = unPaths loc
    pubn = unPaths pub
        

-- | Validate that a group of matched paths are disjoint
disambigmatch
  :: (S.Path a, S.Extend a, S.Tuple (S.Ext a), S.Member (S.Ext a) ~ Maybe a)
  => Paths (Collect [DefnError] a)
  -> Collect [DefnError] (M.Map Ident (Maybe (a -> a)))
disambigmatch = disambig (OlappedMatch . fmap P.K_)



-- | A 'Tuple' definition associates a group of paths with values.
newtype TupDefns a = TupDefns (Paths a)

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun a = Pun (forall x. S.RelPath x => x) a

pun :: Pun a -> TupDefns a
pun (Pun p a) = TupDefns (intro p (Just a))

instance S.Self a => S.Self (Pun a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance S.Local a => S.Local (Pun a) where local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field a => S.Field (Pun a) where
  type Compound (Pun a) = Pun (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

instance S.Self a => S.Self (TupDefns a) where self_ i = pun (S.self_ i)
instance S.Local a => S.Local (TupDefns a) where local_ i = pun (S.local_ i)

instance S.Field a => S.Field (TupDefns a) where
  type Compound (TupDefns a) = Pun (S.Compound a)
  pb #. k = pun (pb S.#. k)

instance S.Let (TupDefns a) where
  type Lhs (TupDefns a) = Path
  type Rhs (TupDefns a) = a
  p #= a = TupDefns (intro p (Just a))

instance S.Sep (TupDefns a) where TupDefns g1 #: TupDefns g2 = TupDefns (g1 <!> g2)
instance S.Splus (TupDefns a) where empty_ = TupDefns zero



-- | A block associates a set of patterns with values
data BlockDefns a = BlockDefns (VisPaths a)

decl :: Path -> BlockDefns a
decl p = BlockDefns (VisPaths ps ps) where ps = intro Nothing p
  
instance S.Self (BlockDefns a) where self_ k = decl (S.self_ k)
  
instance S.Field (BlockDefns a) where
  type Compound (BlockDefns a) = Path
  b #. k = decl (b S.#. k)

instance S.Let (BlockDefns a) where
  type Lhs (BlockDefns a) = Patt
  type Rhs (BlockDefns a) = a
  Patt f #= v = BlockDefns g [m] (pure <$> v)

instance S.Sep (BlockDefns a) where
  BlockDefns g1 #: BlockDefns g2 = BlockDefns (g1 <!> g2)

instance S.Splus (BlockDefns a) where empty_ = BlockDefns zero


-- | A pattern definition represents the simultaneous decomposing a value into distinct
-- parts and the assignment of the parts
newtype Patt = Patt (forall a . F DecompDefns (a -> BlockDefns a))
  deriving (Functor, Applicative, Monad, MonadFree DecomDefns)
newtype DecompDefns a = DecompDefns (Paths a)

letpath :: P.Vis Path -> Patt
letpath p = Patt (pure (BlockDefns . introVis p . Just))
    
matchPun :: Pun Patt -> DecompDefns Patt
matchPun (Pun r p) = DecompDefns (intro r p)

  
instance S.Self (DecompDefns Patt) where self_ i = matchPun (S.self_ i)
instance S.Local (DecompDefns Patt) where local_ i = matchPun (S.local_ i)

instance S.Field (DecompDefns Patt) where
  type Compound (DecompDefns Patt) = Pun (P.Vis Path)
  p #. k = matchPun (p S.#. k)

instance S.Let (DecompDefns Patt) where
  type Lhs (DecompDefns Patt) = Path
  type Rhs (DecompDefns Patt) = Patt
  r #= p = DecompDefns (intro r p)

instance S.Sep (DecompDefns Patt) where
  DecompDefns g1 #: DecompDefns g2 = DecompDefns (g1 <!> g2)

instance S.Splus DecompDefns where empty_ = DecompDefns zero
 
 
instance S.Self (Patt a) where self_ i = letpath (S.self_ i)
instance S.Local (Patt a) where local_ i = letpath (S.local_ i)
  
instance S.Field Patt where
  type Compound Patt = P.Vis Path
  v #. k = letpath (v S.#. k)

type instance S.Member Patt = Patt

instance S.Tuple Patt where
  type Tup Patt = DecompDefns Patt
  tup_ = wrap
  
instance S.Extend Patt where
  type Ext Patt = DecompDefns
  Patt (DecompDefns g1) # DecompDefns g2 = Patt (DecompDefns (g1 <!> g2))



-- | Tree of paths with one or values contained in leaves and zero or more
-- in internal nodes
--
-- Semigroup and monoid instances defined will union subtrees recursively
-- and accumulate values.
data Amb a = a `Overlap` Maybe (Amb a) | Disjoint (M.Map Ident (Amb a))
  deriving (Functor, Foldable, Traversable)
  
instance Applicative Amb where
  pure a = a `Overlap` Nothing
  (<*>) = ap
  
instance Monad Amb where
  return = pure
  
  a `Overlap` Nothing >>= k = k a
  a `Overlap` Just as >>= k = k a <!> (as >>= k)
  Disjoint fa >>= k = Disjoint (M.map (>>= k) fa)
  
instance MonadFree (M.Map Ident) (Amb a) where
  wrap = Disjoint
  
instance Alt (Amb a) where
  x `Overlap` Just a <!> b = (Overlap x . Just) (a <!> b)
  x `Overlap` Nothing <!> b = x `Overlap` Just b
  a <!> x `Overlap` Nothing = x `Overlap` Just a
  a <!> x `Overlap` Just b = (Overlap x . Just) (a <!> b)
  Disjoint fa <!> Disjoint fb = Disjoint (M.unionWith (<!>) fa fb)

