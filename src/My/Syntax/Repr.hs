{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Repr
  ( E
  , runE
  , BlockBuilder(..)
  , DefnError(..)
  , buildBlock
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr
import My.Eval (instantiateDefns, instantiateSelf)
import My.Types.Classes (MyError(..))
import My.Types.Interpreter (K)
import qualified My.Types.Syntax.Class as S
import qualified My.Syntax.Import as S (Deps(..))
import My.Util
import Control.Applicative (liftA2, liftA3, Alternative(..))
import Control.Monad.Trans (lift)
import Control.Monad (ap)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.Foldable (fold, toList)
import Data.Semigroup
import Data.Functor.Alt (Alt(..))
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Typeable
import Data.List (elemIndex, nub)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void
import GHC.Exts (IsString(..))
import Control.Monad.Free
--import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S


-- | Errors from binding definitions
data DefnError =
    OlappedMatch (P.Path P.Key)
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet P.VarPath
  -- ^ Error if a Block assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately
  deriving (Eq, Show, Typeable)
  
  
instance MyError DefnError where
  displayError (OlappedMatch p) = "Ambiguous destructuring of path " ++ show p
  displayError (OlappedSet p) = "Ambiguous assignment to path " ++ show p
  displayError (OlappedVis i) = "Variable assigned with multiple visibilities " ++ show i

  
-- | Builder for a core expression from a parser syntax tree
newtype E a = E (Collect [DefnError] a)
  deriving (Functor, Applicative)
  
runE :: E a -> Either [DefnError] a
runE (E e) = getCollect e

instance Semigroup a => Semigroup (E a) where
  (<>) = liftA2 (<>)
  
instance Monoid a => Monoid (E a) where
  mempty = pure mempty
  mappend = liftA2 mappend
  
instance S.Self a => S.Self (E a) where
  self_ = pure . S.self_
  
instance S.Local a => S.Local (E a) where
  local_ = pure . S.local_
  
instance S.Field a => S.Field (E a) where
  type Compound (E a) = E (S.Compound a)
  
  e #. k = e <&> (S.#. k)

instance Num a => Num (E a) where
  fromInteger = pure . fromInteger
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  
instance Fractional a => Fractional (E a) where
  fromRational = pure . fromRational 
  (/) = liftA2 (/)
  
instance IsString a => IsString (E a) where
  fromString = pure . fromString
  
instance S.Lit a => S.Lit (E a) where
  unop_ op = fmap (S.unop_ op)
  binop_ op a b = liftA2 (S.binop_ op) a b


-- | Build a core expression from a parser syntax tree
type instance S.Member (E (Repr K a)) = E (Repr K a)

instance S.Block (E (Repr K (P.Vis (Nec Ident) P.Key))) where
  type Rec (E (Repr K (P.Vis (Nec Ident) P.Key))) = BlockBuilder (Repr K (P.Vis (Nec Ident) P.Key))
  
  block_ b = Block . fmap P.Priv <$> buildBlock b
  
instance (S.Self a, S.Local a) => S.Tuple (E (Repr K a)) where
  type Tup (E (Repr K a)) = TupBuilder (Repr K a)
  
  tup_ b = Block <$> buildTup b
  
instance S.Extend (E (Repr K a)) where
  type Ext (E (Repr K a)) = E (Defns K (Repr K) a)
  
  e # b = liftA2 Update e b
  
type instance S.Member (E (Defns K (Repr K) (Nec Ident))) =
  E (Repr K (P.Vis (Nec Ident) P.Key))
  
instance S.Block (E (Defns K (Repr K) (Nec Ident))) where
  type Rec (E (Defns K (Repr K) (Nec Ident))) =
    BlockBuilder (Repr K (P.Vis (Nec Ident) P.Key))
  
  block_ = buildBlock
  
type instance S.Member (E (Defns K (Repr K) (P.Vis (Nec Ident) P.Key))) = 
  E (Repr K (P.Vis (Nec Ident) P.Key))
  
instance S.Block (E (Defns K (Repr K) (P.Vis (Nec Ident) P.Key))) where
  type Rec (E (Defns K (Repr K) (P.Vis (Nec Ident) P.Key))) =
    BlockBuilder (Repr K (P.Vis (Nec Ident) P.Key))
    
  block_ b = fmap P.Priv <$> buildBlock b
  
instance S.Tuple (E (Defns K (Repr K) (P.Vis (Nec Ident) P.Key))) where
  type Tup (E (Defns K (Repr K) (P.Vis (Nec Ident) P.Key))) =
    TupBuilder (Repr K (P.Vis (Nec Ident) P.Key))
  
  tup_ = buildTup

type instance S.Member (BlockBuilder (Repr K (P.Vis (Nec Ident) P.Key))) =
  E (Repr K (P.Vis (Nec Ident) P.Key))

instance S.Deps (BlockBuilder (Repr K (P.Vis (Nec Ident) P.Key))) where
  prelude_ (BlockB v) b = b' S.#: b
    where
      -- Build a pattern that introduces a local alias for each
      -- component of the imported prelude Block
      b' :: BlockBuilder (Repr K (P.Vis (Nec Ident) P.Key))
      b' = S.tup_ (foldr puns S.empty_ ns) S.#= S.block_ (BlockB v)
      
      puns :: (S.Splus a, S.Local a) => Ident -> a -> a
      puns i a = S.local_ i S.#: a

      -- identifiers for public component names of prelude Block
      ns = mapMaybe ident (names (self v))
      
      ident :: P.Key -> Maybe Ident
      ident (P.K_ i) = Just i
    
  
  
-- | Build a 'Defns' expression from a parser 'Block' syntax tree.
buildTup :: Monad m => TupBuilder (m a) -> E (Defns K m a)
buildTup (TupB g xs) = liftA2 substexprs (lnode g) (rexprs xs)
  where
    substexprs nd xs = Defns []
      (fmap (xs'!!) <$> M.mapKeysMonotonic (Key . coerce) nd) where
      xs' = lift <$> xs
  
    -- Right-hand side values to be assigned
    rexprs :: [E a] -> E [a]
    rexprs xs = sequenceA xs
    
    -- Left-hand side paths determine constructed shape
    lnode
      :: GroupBuilder P.Key -> E (M.Map P.Key (Node K Int))
    lnode g =
      E (M.traverseMaybeWithKey (extractnode . P.Pub . Pure) (build g [0..]))
  
    
-- | Validate that a finished tree has unambiguous paths and construct 
--   a 'Node' expression that reflects the tree of assigned values.
--
--   If there are any ambiguous paths, returns them as list of 'OlappedSet'
--   errors.
--
--   Paths with missing values represent paths that must not be assigned
--   and are not included in the constructed 'Node'.
extractnode
  :: P.VarPath
  -- ^ Path to the node being extracted
  -> An P.Key (Maybe x)
  -- ^ Paths to validate and extract from
  -> Collect [DefnError] (Maybe (Node K x))
  -- ^ Extracted (possibly empty) node of paths
extractnode _ (An a Nothing) = pure (Closed <$> a)
extractnode p (An a (Just b)) = (collect . pure) (OlappedSet p)
    *> extractnode p b
extractnode p (Un m) = Just . Open . M.mapKeysMonotonic (Key . coerce)
  <$> M.traverseMaybeWithKey
    (\ k -> extractnode (bimap (Free . (`P.At` k)) (Free . (`P.At` k)) p))
    m


-- | Build a group by merging series of paths
data GroupBuilder i = GroupB
  { size :: Int
    -- ^ number of values to assign / paths
  , build :: forall f a. (MonadFree (M.Map P.Key) f, Alt f) => [a] -> M.Map i (f (Maybe a))
    -- ^ function for constructing tree
  , names :: [i]
    -- ^ list of top-level fields in assignment order
  }

instance Ord i => Semigroup (GroupBuilder i) where
  GroupB sz1 b1 n1 <> GroupB sz2 b2 n2 =
    GroupB (sz1 + sz2) b (n1 <> n2)
    where
      b
        :: forall f a . (MonadFree (M.Map P.Key) f, Alt f)
        => [a]
        -> M.Map i (f (Maybe a))
      b xs = let (x1, x2) = splitAt sz1 xs in M.unionWith (<!>) (b1 x1) (b2 x2)
  
instance Ord i => Monoid (GroupBuilder i) where
  mempty = GroupB 0 mempty mempty
  
  mappend = (<>)
  

-- | Build up a sequence of nested fields, remembering the top-level name
data PathBuilder i =
  PathB
    (forall f a . (MonadFree (M.Map P.Key) f, Alt f) => f a -> f a)
    -- ^ push additional fields onto path
    i
    -- ^ top-level field name

intro :: PathBuilder i -> GroupBuilder i
intro (PathB f n) = GroupB 1 (M.singleton n . f . pure . pure . head) [n]

-- | Build a path and value for a punned assignment
data PunBuilder a =
  PunB
    (PathBuilder P.Key)
    -- ^ Punned path
    a
    -- ^ Value corresponding to path in environment

-- | Build the tree of fields and corresponding values for a tuple group
data TupBuilder a =
  TupB
    (GroupBuilder P.Key)
    -- ^ Constructs tree of fields assigned by statements in a tuple
    [E a]
    -- ^ List of values in assignment order
  
  
pun :: PunBuilder (E a) -> TupBuilder a
pun (PunB p a) = TupB (intro p) [a]
    
-- class instances
instance S.Self (PathBuilder P.Key) where
  self_ i = PathB id (P.K_ i)
  
instance S.Local (PathBuilder Ident) where
  local_ i = PathB id i
  
instance S.Field (PathBuilder a) where
  type Compound (PathBuilder a) = PathBuilder a
  PathB f a #. i = PathB (f . wrap . M.singleton (P.K_ i)) a

instance S.Self a => S.Self (PunBuilder a) where
  self_ i = PunB (S.self_ i) (S.self_ i)
  
instance S.Local a => S.Local (PunBuilder a) where
  local_ i = PunB (S.self_ i) (S.local_ i)

instance S.Field a => S.Field (PunBuilder a) where
  type Compound (PunBuilder a) = PunBuilder (S.Compound a)
  
  PunB f x  #. i = PunB (f S.#. i) (x S.#. i)

instance S.Self a => S.Self (TupBuilder a) where
  self_ i = pun (S.self_ i)
  
instance S.Local a => S.Local (TupBuilder a) where
  local_ i = pun (S.local_ i)
  
instance S.Field a => S.Field (TupBuilder a) where
  type Compound (TupBuilder a) = PunBuilder (E (S.Compound a))
  
  b #. k = pun (b S.#. k)
  
instance S.Let (TupBuilder a) where
  type Lhs (TupBuilder a) = PathBuilder P.Key
  type Rhs (TupBuilder a) = E a
  
  p #= x = TupB (intro p) [x]
    
instance S.Sep (TupBuilder a) where
  TupB g1 a1 #: TupB g2 a2 = TupB (g1 <> g2) (a1 <> a2)
    
instance S.Splus (TupBuilder a) where
  empty_ = TupB mempty mempty
  

-- | Build definitions set from a list of parser recursive statements from
-- a Block.
buildBlock
  :: BlockBuilder (Repr K (P.Vis (Nec Ident) P.Key))
  -> E (Defns K (Repr K) (Nec Ident))
buildBlock (BlockB v) = liftA2 substexprs (ldefngroups v) (rexprs v)
  where
    substexprs (en, se) xs =
      Defns
        (map (updateenv (substnode <$> en) M.!) ls)
        (substnode <$> M.mapKeysMonotonic (Key . coerce) se)
      where
        substnode = fmap (xs'!!)
        xs' = abstrec ls ks <$> xs
    
    -- Use the source order for private definition list to make predicting
    -- output expressions easier (alternative would be sorted order)
    ls = (nub . names) (local v)
    ks = (nub . names) (self v)
    
    ldefngroups
      :: VisBuilder a
      -> E (M.Map Ident (Node K Int), M.Map P.Key (Node K Int))
    ldefngroups v = E (extractdefngroups (b1 [0..sz1], b2 [sz1..]))
      where
        GroupB {size = sz1, build = b1} = local v
        GroupB {size = sz2, build = b2} = self v
    
    rexprs :: VisBuilder (E ([a], [a])) -> E [a]
    rexprs v = uncurry (++) <$> values v
    
    
    
-- | Validate that a group of private/public definitions are disjoint, and
--   extract 'Node' expressions for each defined name.
extractdefngroups
  :: (M.Map Ident (An P.Key (Maybe x)), M.Map P.Key (An P.Key (Maybe x)))
  -> Collect [DefnError] (M.Map Ident (Node K x), M.Map P.Key (Node K x))
extractdefngroups (en, se) = viserrs *> bitraverse
    (M.traverseMaybeWithKey (extractnode . P.Priv . Pure))
    (M.traverseMaybeWithKey (extractnode . P.Pub . Pure))
    (en, se)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    viserrs = M.foldrWithKey
      (\ l (a, b) e -> e *> (collect . pure) (OlappedVis l))
      (pure ())
      comb
      
    -- Find pairs of public and private definitions for the same identifier
    comb = M.intersectionWith (,) en (filterKey se)
    
    -- Find corresponding 'Idents' for a map of 'P.Key's
    filterKey = M.fromAscList
      . mapMaybe (\ (k, a) -> case k of P.K_ l -> Just (l, a)) . M.toAscList

    
-- | Attach optional bindings to the environmental values corresponding to open
--   node definitions, so that private definitions shadow environmental ones on
--   a path basis - e.g. a path declared x.y.z = ... will shadow the .y.z path
--   of any x variable in scope. 
updateenv
  :: M.Map Ident (Node K (Rec K (Repr K) (Nec Ident)))
  -> M.Map Ident (Rec K (Repr K) (Nec Ident))
updateenv = M.mapWithKey (\ k n -> case n of
  Closed a -> a
  Open fa -> updateField (return (Nec Opt k)) fa)
  where
    updateField
      :: Rec K (Repr K) a
      -> M.Map K (Node K (Rec K (Repr K) a))
      -> Rec K (Repr K) a
    updateField e n =
      (wrap . Update (unwrap e) . Defns []) (fmap (lift . unwrap) <$> n)
  
    unwrap :: Rec K m a -> m (Var K (m (Var Int (Scope K m a))))
    unwrap = unscope . unscope . getRec
    
    wrap :: m (Var K (m (Var Int (Scope K m a)))) -> Rec K m a
    wrap = Rec . Scope . Scope
    
   
-- | Abstract a set of private/public bindings in an expression
abstrec
  :: Monad m
  => [Ident]
  -- ^ Names bound privately
  -> [P.Key]
  -- ^ Names bound publicly
  -> m (P.Vis (Nec Ident) P.Key)
  -- ^ Expression with bound names free
  -> Rec (Tag k) m (Nec Ident)
  -- ^ Expression with bound names abstracted
abstrec ls ks = abstractRec
  (\ x@(Nec _ l) -> maybe (Right x) Left (l `elemIndex` ls))
  (\ v -> case v of
      P.Pub k -> (Left . Key) (coerce k)
      P.Priv x@(Nec _ l) -> if P.K_ l `elem` ks 
        then Left (Key l)
        else Right x)

    
-- | Build a group of name definitions partitioned by public/private visibility
data VisBuilder a = VisB 
  { local :: GroupBuilder Ident
    -- ^ Builder for tree of locally defined values
  , self :: GroupBuilder P.Key
    -- ^ Builder for tree of publicly defined values
  , values :: a
    -- ^ Local and publicly defined values
  }
  deriving Functor
  
instance (Semigroup a) => Semigroup (VisBuilder a) where
  VisB l1 s1 v1 <> VisB l2 s2 v2 =
    VisB (l1 <> l2) (s1 <> s2) (v1 <> v2)
  
instance (Monoid a) => Monoid (VisBuilder a) where 
  mempty = VisB mempty mempty mempty
  
  VisB l1 s1 v1 `mappend` VisB l2 s2 v2 =
    VisB (l1 `mappend` l2) (s1 `mappend` s2) (v1 `mappend` v2)

    
-- | Build the tree of paths assigned to by a pattern, and a deconstructor for
-- the assigned value
newtype PattBuilder =
  PattB
    (forall k a .
      VisBuilder (E (Repr (Tag k) a -> ([Repr (Tag k) a], [Repr (Tag k) a]))))

letpath :: P.Vis (PathBuilder Ident) (PathBuilder P.Key) -> PattBuilder
letpath p = case p of 
  P.Pub p -> PattB (VisB {local = mempty, self = intro p, values = pure wrappub})
  P.Priv p -> PattB (VisB {local = intro p, self = mempty, values = pure wrappriv})
  where
    wrappub e = ([], [e])
    wrappriv e = ([e], [])
  
letungroup :: PattBuilder -> Ungroup -> PattBuilder
letungroup (PattB b1) (Ungroup (PattB b2) n) =
  PattB (b1' <> b2)
    where
      b1'
        :: VisBuilder (E (Repr (Tag k) a -> ([Repr (Tag k) a], [Repr (Tag k) a])))
      b1' = fmap rest <$> b1
      
      rest :: (Repr (Tag k) a -> b) -> Repr (Tag k) a -> b
      rest f e = f (hide (nub n) e)

      -- | Folds over a value to find keys to restrict for an expression.
      --
      -- Can be used as function to construct an expression of the 'left-over' components
      -- assigned to nested ungroup patterns.
      hide :: Foldable f => f P.Key -> Repr (Tag k) a -> Repr (Tag k) a
      hide ks e = foldl (\ e k -> e `Fix` Key (coerce k)) e ks
    
-- | An ungroup pattern
data Ungroup =
  Ungroup
    PattBuilder
    -- ^ Builds the set of local and public assignments made by rhs patterns, where
    -- assigned values are obtained by deconstructing an original value
    [P.Key]
    -- ^ List of fields of the original value used to obtain deconstructed values

ungroup :: UngroupBuilder -> Ungroup
ungroup (UngroupB g ps) =
  Ungroup (PattB (liftA2 applyDecomp (ldecomp g) <$> rpatt ps)) (names g)
  where
    ldecomp :: GroupBuilder P.Key -> E (Repr (Tag k) a -> [Repr (Tag k) a])
    ldecomp g = pattdecomp <$>
      (M.traverseMaybeWithKey (extractdecomp . Pure) . build g . repeat) (pure pure)
  
    applyDecomp :: Monoid b => (a -> [a]) -> [a -> b] -> (a -> b)
    applyDecomp s fs a = fold (zipWith ($) fs (s a))
    
    rpatt :: [PattBuilder] -> VisBuilder (E [Repr (Tag k) a -> ([Repr (Tag k) a], [Repr (Tag k) a])])
    rpatt = foldMap (\ (PattB v) -> fmap pure <$> v)
      
      
-- | Build an tree of paths to assign using the parts of a deconstructed value
data UngroupBuilder =
  UngroupB
    (GroupBuilder P.Key)
    -- ^ Build tree of selected parts to be deconstructed from a value
    [PattBuilder]
    -- ^ Patterns for assigning parts of deconstructed value
 
instance S.Sep UngroupBuilder where
  UngroupB b1 v1 #: UngroupB b2 v2 = UngroupB (b1 <> b2) (v1 <> v2)
  
instance S.Splus UngroupBuilder where
  empty_ = UngroupB mempty mempty
  
matchPun :: PunBuilder PattBuilder -> UngroupBuilder
matchPun (PunB x p) = UngroupB (intro x) [p]
    
-- | Build a recursive Block group
newtype BlockBuilder a = BlockB (VisBuilder (E ([a], [a])))
  
decl :: PathBuilder P.Key -> BlockBuilder a
decl (PathB f n) = BlockB (mempty {self = declg})
  where
    declg :: GroupBuilder P.Key
    declg = GroupB
      {size=0, build = (pure . M.singleton n . f) (pure Nothing), names = [n]}
    

-- class instances
instance S.Self (BlockBuilder a) where
  self_ k = decl (S.self_ k)
  
instance S.Field (BlockBuilder a) where
  type Compound (BlockBuilder a) = PathBuilder P.Key
  
  b #. k = decl (b S.#. k)
  

instance S.Let (BlockBuilder (Repr (Tag k) a)) where
  type Lhs (BlockBuilder (Repr (Tag k) a)) = PattBuilder
  type Rhs (BlockBuilder (Repr (Tag k) a)) = E (Repr (Tag k) a)
  
  PattB b #= a = BlockB ((<*> a) <$> b)
      
instance S.Sep (BlockBuilder a) where
  BlockB va #: BlockB vb = BlockB (va <> vb)
  
instance S.Splus (BlockBuilder a) where
  empty_ = BlockB mempty
    
instance S.Self PattBuilder where
  self_ i = letpath (S.self_ i)
  
instance S.Local PattBuilder where
  local_ i = letpath (S.local_ i)
  
instance S.Field PattBuilder where
  type Compound PattBuilder = P.Vis (PathBuilder Ident) (PathBuilder P.Key)
  v #. k = letpath (v S.#. k)

type instance S.Member PattBuilder = PattBuilder

instance S.Tuple PattBuilder where
  type Tup PattBuilder = UngroupBuilder
  
  tup_ g = p
    where 
      Ungroup p _ = ungroup g
  
instance S.Extend PattBuilder where
  type Ext PattBuilder = Ungroup
  
  (#) = letungroup

type instance S.Member Ungroup = PattBuilder

instance S.Tuple Ungroup where
  type Tup Ungroup = UngroupBuilder
  
  tup_ = ungroup
  
  
instance S.Local UngroupBuilder where
  local_ i = matchPun (S.local_ i)
  
instance S.Self UngroupBuilder where
  self_ k = matchPun (S.self_ k)
  
instance S.Field UngroupBuilder where
  type Compound UngroupBuilder =
    PunBuilder (P.Vis (PathBuilder Ident) (PathBuilder P.Key))
  
  p #. k = matchPun (p S.#. k)
  
instance S.Let UngroupBuilder where
  type Lhs UngroupBuilder = PathBuilder P.Key
  type Rhs UngroupBuilder = PattBuilder
  
  x #= p = UngroupB (intro x) [p]
    
    
-- | Unfold a set of matched fields into a decomposing function
pattdecomp :: (S.Path a, Monoid b) => M.Map P.Key (a -> b) -> (a -> b)
pattdecomp = M.foldMapWithKey (\ (P.K_ i) f a -> f (a S.#. i))
    
    
-- | Validate a nested group of matched paths are disjoint, and extract
-- a decomposing function
extractdecomp
  :: (S.Path a, Monoid b)
  => P.Path P.Key
  --  ^ Path to nested match group
  -> An P.Key (Maybe (E (a -> b)))
  -- ^ Group of matched paths to nested patterns
  -> E (Maybe (a -> b))
  -- ^ Value decomposition function
extractdecomp _ (An a Nothing) = sequenceA a
extractdecomp p (An a (Just b)) = (E . collect . pure) (OlappedMatch p)
  *> sequenceA a
  *> extractdecomp p b
extractdecomp p (Un ma) = Just . pattdecomp 
  <$> M.traverseMaybeWithKey (extractdecomp . Free . P.At p) ma

  
-- | Tree of paths with one or values contained in leaves and zero or more
--   in internal nodes
--
--   Semigroup and monoid instances defined will union subtrees recursively
--   and accumulate values.
data An k a = An a (Maybe (An k a)) | Un (M.Map k (An k a))
  deriving (Functor, Foldable, Traversable)
  
instance Ord k => Applicative (An k) where
  pure a = An a Nothing
  (<*>) = ap
  
instance Ord k => Monad (An k) where
  return = pure
  
  An a Nothing >>= k = k a
  An a (Just as) >>= k = k a <!> (as >>= k)
  Un ma >>= k = Un ((>>= k) <$> ma)
  
instance Ord k => MonadFree (M.Map k) (An k) where
  wrap = Un
  
instance Ord k => Alt (An k) where
  An x (Just a) <!> b = (An x . Just) (a <!> b)
  An x Nothing <!> b = An x (Just b)
  a <!> An x Nothing = An x (Just a)
  a <!> An x (Just b) = (An x . Just) (a <!> b)
  Un ma <!> Un mb = Un (M.unionWith (<!>) ma mb)

