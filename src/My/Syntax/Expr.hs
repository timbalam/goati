{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving #-}
--{-# OverloadedStrings, ExistentialQuantification, ScopedTypeVariables #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Expr
  ( expr
  , program
  , DefnError(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Expr hiding (B)
import My.Types.Classes (MyError(..))
import My.Types.Interpreter (K)
import qualified My.Types.Syntax.Class as S
import My.Parser (ShowMy(..))
import My.Util
import Control.Applicative (liftA2, liftA3, Alternative(..))
import Control.Monad.Trans (lift)
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable (fold, toList)
import Data.Semigroup
import Data.Functor.Alt (Alt(..))
import Data.Maybe (mapMaybe)
import Data.Typeable
import Data.List (elemIndex, nub)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Void
import Control.Monad.Free
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S


-- | Errors from binding definitions
data DefnError =
    OlappedMatch (P.Path Key)
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet P.VarPath
  -- ^ Error if a block assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately
  deriving (Eq, Show, Typeable)
  
  
instance MyError DefnError where
  displayError (OlappedMatch p) = "Ambiguous destructuring of path " ++ showMy p
  displayError (OlappedSet p) = "Ambiguous assignment to path " ++ showMy p
  displayError (OlappedVis i) = "Variable assigned with multiple visibilities " ++ showMy i

  
-- | Builder for a core expression from a parser syntax tree
newtype B a = B (Collect [DefnError] a)
  deriving (Functor, Applicative)
  
deriving instance Foldable B
  
getB :: B a -> Either [DefnError] a
getB (B e) = getCollect e

instance Semigroup a => Semigroup (B a) where
  B a <> B b = B (liftA2 (<>) a b)
  
instance Monoid a => Monoid (B a) where
  mempty = B (pure mempty)
  
  B a `mappend` B b = B (liftA2 mappend a b)
  
instance S.Self a => S.Self (B a) where
  self_ = pure . S.self_
  
instance S.Local a => S.Local (B a) where
  local_ = pure . S.local_
  
instance S.Field a => S.Field (B a) where
  type Compound (B a) = B a
  
  e #. k = e <&> (#. k)
  
instance S.Field a => S.Path (B a)
  
instance S.Lit a => S.Lit (B a) where
  int_ = pure . S.int_
  str_ = pure . S.str_
  num_ = pure . S.num_
  
  unop_ op = fmap (S.unop_ op)
  binop_ op a b = liftA2 (S.binop_ op) a b


-- | Build a core expression from a parser syntax tree
type instance S.Member (B (Expr K a)) = B (Expr K a)

instance S.Block (B (Expr K (P.Name (Nec Ident) Key a))) where
  type Rec (B (Expr K (P.Name (Nec Ident) Key a))) = BlockBuilder (Expr K (P.Name (Nec Ident) Key a))
  
  block_ b = Block . (first P.Priv <$>) <$> block b
  
instance S.Tuple (B (Expr K a)) where
  type Tup (B (Expr K a)) = TupBuilder (Expr K a)
  
  tup_ b = Block <$> tup b
  
instance S.Extend (B (Expr K a)) where
  type Ext (B (Expr K a)) = B (Defns K (Expr K) a)
  
  (#) = liftA2 Update
  
instance S.Block (B (Defns K (Expr K) (P.Name (Nec Ident) Key a))) where
  type Rec (B (Defns K (Expr K) (P.Name (Nec Ident) Key a))) =
    BlockBuilder (Expr K (P.Name (Nec Ident) Key a))
  
  block_ b = (first P.Priv <$>) <$> block b
  
instance S.Tuple (B (Defns K (Expr K) a)) where
  type Tup (B (Defns K (Expr K) a)) = TupBuilder (Expr K a)
  
  tup_ b = tup b

          
-- | Build a 'Defns' expression from a parser 'Block' syntax tree.
tup :: TupBuilder (Expr K a) -> B (Defns K (Expr K) a)
tup (TupB g) = liftA2 substexprs (lnode xs) (rexprs xs)
  where
    substexprs nd xs = Defns [] (((xs'!!) <$>) <$> M.mapKeysMonotonic Key nd)
      where
        xs' = map lift xs
  
    -- Right-hand side values to be assigned
    rexprs :: GroupBuilder (B (Expr a)) -> B [Expr K a]
    rexprs b = sequenceA (values b)
    
    -- Left-hand side paths determine constructed shape
    lnode
      :: GroupBuilder (B (Expr a)) -> B (M.Map Key (Node K Int))
    lnode g =
      B (M.traverseMaybeWithKey (extractnode . P.Pub . Pure) (getM (build g [0..])))
  

-- | Build a 'Defns' expression from 'S.RecStmt's as parsed from the top level of
--   a file
program
  :: NonEmpty (P.RecStmt (P.Expr (P.Name Ident Key a)))
  -> Either [DefnError] (Defns K (Expr K) (P.Res (Nec Ident) a))
program xs = (getCollect . block) (toList xs)
  
    
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
  -> An Key (Maybe x)
  -- ^ Paths to validate and extract from
  -> Collect [DefnError] (Maybe (Node K x))
  -- ^ Extracted (possibly empty) node of paths
extractnode _ (An a Nothing) = pure (Closed <$> a)
extractnode p (An a (Just b)) = (collect . pure) (OlappedSet p)
    *> extractnode p b
extractnode p (Un ma) = Just . Open . M.mapKeysMonotonic Key
  <$> M.traverseMaybeWithKey
    (\ k -> extractnode (bimap (Free . (`P.At` k)) (Free . (`P.At` k)) p))
    (getM ma)


-- | Build a group by merging series of paths
data GroupBuilder i = GroupB
  { size :: Int
    -- ^ number of values to assign / paths
  , build :: forall f a. (MonadFree (M.Map Key) f, Alt f) => [a] -> M.Map i (f (Maybe a))
    -- ^ function for constructing tree
  , names :: [i]
    -- ^ list of top-level fields in assignment order
  }

instance Semigroup (GroupBuilder i) where
  GroupB sz1 b1 n1 <> GroupB sz2 b2 n2 =
    GroupB (sz1 + sz2) b (n1 <> n2)
    where
      b xs = let (x1, x2) = splitAt sz1 xs in M.unionWith (<!>) (b1 x1) (b2 x2)
  
instance Monoid (GroupBuilder i) where
  mempty = GroupB 0 mempty mempty
  
  mappend = (<>)
  

-- | Build up a sequence of nested fields, remembering the top-level name
data PathBuilder i =
  PathB
    (forall f a . (MonadFree (M.Map Key) f, Alt f) => f a -> f a)
    -- ^ push additional fields onto path
    i
    -- ^ top-level field name

intro :: PathBuilder i -> GroupBuilder i
intro (PathB f n) = GroupB 1 (M.singleton i . f . pure . pure . head) [n]

-- | Build a path and value for a punned assignment
data PunBuilder a =
  PunB
    (PathBuilder Key)
    -- ^ Punned path
    a
    -- ^ Value corresponding to path in environment

-- | Build the tree of fields and corresponding values for a tuple group
data TupBuilder a =
  TupB
    (GroupBuilder Key)
    -- ^ Constructs tree of fields assigned by statements in a tuple
    [B a]
    -- ^ List of values in assignment order
    
instance Semigroup (TupBuilder a) where
  TupB g1 a1 <> TupB g2 a2 = TupB (g1 <> g2) (a1 <> a2)
    
instance Monoid (TupBuilder a) where
  mempty = TupB mempty mempty
  
  mappend = (<>)
  
  
pun :: PunBuilder b -> TupBuilder a
pun (PunB p a) = TupB (intro p) [a]
    
-- class instances
instance S.Self (PathBuilder Key) where
  self_ k = PathB id k
  
instance S.Local (PathBuilder Ident) where
  local_ i = PathB id i
  
instance S.Field (PathBuilder i) where
  type Compound (PathBuilder i) = PathBuilder i
  
  PathB f i #. k = PathB (f . wrap . M.singleton k) i
  
instance S.Path (PathBuilder i)

instance S.Self a => S.Self (PunBuilder a) where
  self_ k = PunB (S.self_ k) (S.self_ k)
  
instance S.Local a => S.Local (PunBuilder a) where
  local_ i = PunB (S.self_ (K_ i)) (S.local_ i)

instance S.Field a => S.Field (PunBuilder a) where
  type Compound (PunBuilder a) = PunBuilder a
  
  PunB f x  #. k = PunB (f S.#. k) (x S.#. k)
  
instance S.Path a => S.Path (PunBuilder a)

instance S.Self a => S.Self (TupBuilder a) where
  self_ k = pun (S.self_ k)
  
instance S.Local a => S.Local (TupBuilder a) where
  local_ i = pun (S.local_ i)
  
instance S.Field a => S.Field (TupBuilder a) where
  type Compound (TupBuilder a) = PunBuilder (B a)
  
  b #. k = pun (b S.#. k)
  
instance S.Field a => S.VarPath (TupBuilder a)
  
instance S.Let (TupBuilder a) where
  type Lhs (TupBuilder a) = PathBuilder Key
  type Rhs (TupBuilder a) = B a
  
  p #= x = TupB (intro p) [x]
  
instance S.TupStmt (TupBuilder a)
  

-- | Build definitions set from a list of parser recursive statements from
--   a block.
block
  :: forall a . BlockBuilder (Expr K (P.Name (Nec Ident) Key a))
  -> B (Defns K (Expr K) (P.Res (Nec Ident) a))
block (BlockB v) = liftA2 substexprs (ldefngroups v) (rexprs v)
  where
    substexprs (en, se) xs =
      Defns
        ((flip map ls . (M.!) . updateenv) (substnode <$> en))
        (substnode <$> M.mapKeysMonotonic Key se)
      where
        substnode = ((xs'!!) <$>)
        xs' = abstrec ls ks <$> xs
    
    -- Use the source order for private definition list to make predicting
    -- output expressions easier (alternative would be sorted order)
    (ls, ks) = (nub (names (local v)), nub (names (self v)))
    
    ldefngroups
      :: VisBuilder (Expr K (P.Name (Nec Ident) Key a))
      -> B (M.Map Ident (Node K Int), M.Map Key (Node K Int))
    ldefngroups v = extractdefngroups (b1 [0..sz1], b2 [sz1..])
      where
        GroupB { size = sz1, build = b1 } = local v
        GroupB { size = sz2, build = b2 } = self v
    
    rexprs
      :: VisBuilder (Expr K (P.Name (Nec Ident) Key a))
      -> B [Expr K (P.Name (Nec Ident) Key a)]
    rexprs v = localValues v <> selfValues v
    
    
    
-- | Validate that a group of private/public definitions are disjoint, and
--   extract 'Node' expressions for each defined name.
extractdefngroups
  :: (M.Map Ident (An Key (Maybe x)), M.Map Key (An Key (Maybe x)))
  -> Collect [DefnError] (M.Map Ident (Node K x), M.Map Key (Node K x))
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
    
    -- Find corresponding 'Idents' for a map of 'Key's
    filterKey = M.fromAscList
      . mapMaybe (\ (k, a) -> case k of K_ l -> Just (l, a)) . M.toAscList

    
-- | Attach optional bindings to the environmental values corresponding to open
--   node definitions, so that private definitions shadow environmental ones on
--   a path basis - e.g. a path declared x.y.z = ... will shadow the .y.z path
--   of any x variable in scope. 
updateenv
  :: M.Map Ident (Node K (Rec K (Expr K) (P.Res (Nec Ident) a)))
  -> M.Map Ident (Node K (Rec K (Expr K) (P.Res (Nec Ident) a)))
updateenv = M.mapWithKey (\ k n -> case n of
  Closed _ -> n
  Open fa -> Closed ((updateField . return . P.In) (Nec Opt k) fa))
  where
    updateField
      :: Rec K (Expr K) a
      -> M.Map K (Node K (Rec K (Expr K) a))
      -> Rec K (Expr K) a
    updateField e n =
      (wrap . Update (unwrap e) . Defns []) ((lift . unwrap <$>) <$> n)
  
    unwrap :: Rec K m a -> m (Var K (m (Var Int (Scope K m a))))
    unwrap = unscope . unscope . getRec
    
    wrap :: m (Var K (m (Var Int (Scope K m a)))) -> Rec K m a
    wrap = Rec . Scope . Scope
    
   
-- | Abstract a set of private/public bindings in an expression
abstrec
  :: [Ident]
  -- ^ Names bound privately
  -> [Key]
  -- ^ Names bound publicly
  -> Expr K (P.Name (Nec Ident) Key a)
  -- ^ Expression with bound names free
  -> Rec K (Expr K) (P.Res (Nec Ident) a)
  -- ^ Expression with bound names abstracted
abstrec ls ks = abstractRec
  (bitraverse
    (\ x@(Nec _ l) -> maybe (Right x) Left (l `elemIndex` ls))
    pure)
  (bitraverse
    (\ v -> case v of
      P.Pub k -> Left (Key k)
      P.Priv x@(Nec _ l) -> if K_ l `elem` ks 
        then (Left . Key) (K_ l)
        else Right x)
    pure)

    
-- | Build a group of name definitions partitiioned by public/private visibility
data VisBuilder a = VisB 
  { local :: GroupBuilder Ident
    -- ^ Builder for tree of locally defined values
  , localValues :: a
    -- ^ Locally defined values
  , self :: GroupBuilder Key
    -- ^ Builder for tree of publicly defined values
  , selfValues :: a
    -- ^ Publicly defined values
  }
  deriving Functor
  
instance (Semigroup a) => Semigroup (VisBuilder a) where
  VisB l1 lv1 s1 sv1 <> VisB l2 lv2 s2 sv2 =
    VisB (l1 <> l2) (lv1 <> lv2) (s1 <> s2) (sv1 <> sv2)
  
instance (Monoid a) => Monoid (VisBuilder a) where 
  mempty = VisB mempty mempty mempty mempty
  
  VisB l1 lv1 s1 sv1 `mappend` VisB l2 lv2 s2 sv2 =
    VisB (l1 `mappend` l2) (lv1 `mappend` lv2) (s1 `mappend` s2) (sv1 `mappend` sv2)

    
-- | Build the tree of paths assigned to by a pattern, and a deconstructor for the assigned
-- value
data PattBuilder =
  PattB
    (forall k a . S.Path a => VisBuilder (B (a -> [a])))
    -- ^ Builds the set of local and public assignments made in a pattern, where
    -- assigned values are obtained by deconstructing an original value
    [Key]
    -- ^ List of fields of the original value used to obtain deconstructed values

letpath :: P.Vis (PathBuilder Ident) (PathBuilder Key) -> PattBuilder
letpath (P.Pub p) = PattB (VisB { self = intro p, selfValues = pure pure })
letpath (P.Priv p) = PattB (VisB { local = intro p, localValues = pure pure })

ungroup :: UngroupBuilder -> PattBuilder
ungroup (UngroupB g ps) =
  liftA2 applyDecomp (ldecomp g) <$> rpatt ps
  where
    ldecomp :: S.Path a => GroupBuilder Key -> B (a -> [a])
    ldecomp g = pattdecomp <$>
      (M.traverseMaybeWithKey (extractdecomp . Pure . Pub) . build g . repeat) (pure pure)
  
    applyDecomp :: (a -> [a]) -> [a -> [a]] -> (a -> [a])
    applyDecomp s fs = zipWith ($) fs . s
    
    rpatt :: S.Path a => [PattBuilder] -> VisBuilder (B [a -> [a]])
    rpatt = foldMap (\ (PattB v _) -> fmap pure <$> v)
    
    
instance Monoid PattBuilder where
  mempty = PattB mempty mempty
 
  PattB b1 n1 `mappend` PattB b2 n2 =
    PattB (b1' <> b2) (n1 <> n2)
    where
      b1' = b1 { localValues = localValues b1 . hide n2, selfValues = selfValues b1 . hide n2 }

      -- | Folds over a value to find keys to restrict for an expression.
      --
      -- Can be used as function to construct an expression of the 'left-over' components
      -- assigned to nested ungroup patterns.
      hide :: Foldable f => f Key -> Expr (Tag k) a -> Expr (Tag k) a
      hide ks e = foldl (\ e k -> e `Fix` Key k) e ks
      
  
-- | Build an tree of paths to assign using the parts of a deconstructed value
data UngroupBuilder =
  UngroupB
    (GroupBuilder Key)
    -- ^ Build tree of selected parts to be deconstructed from a value
    [PattBuilder]
    -- ^ Patterns for assigning parts of deconstructed value

    
instance Semigroup UngroupBuilder where
  UngroupB b1 v1 <> UngroupB b2 v2 = UngroupB (b1 <> b2) (v1 <> v2)
  
instance Monoid UngroupBuilder where
  mempty = Ungroup mempty mempty
  
  mappend = (<>)
  
matchPun :: PunBuilder PattBuilder -> UngroupBuilder
matchPun (PunB x p) = UngroupB (intro x) [p]
    
-- | Build a recursive block group
newtype BlockBuilder a = BlockB (VisBuilder (B [a]))
  deriving (Semigroup, Monoid)
  
decl :: PathBuilder Key -> BlockBuilder a
decl (PathB f n) =
  BlockB (mempty { self = mempty { build = const (f (pure Nothing)), names = [n] } })

-- class instances
instance S.Self (BlockBuilder a) where
  self_ k = decl (S.self_ k)
  
instance S.Field (BlockBuilder a) where
  type Compound (BlockBuilder a) = PathBuilder Key
  
  b #. k = decl (b #. k)
  
instance S.Path a => S.Let (BlockBuilder a) where
  type Lhs (BlockBuilder a) = PattBuilder
  type Rhs (BlockBuilder a) = B a
  
  PattB b #= a = BlockB (VisB
    { local = local b
    , localValues = localValues b <*> a
    , self = self b
    , selfValues = selfValues b <*> a
    })
  
instance S.RecStmt (BlockBuilder a)
    
instance S.Self PattBuilder where
  self_ i = letPath (S.self_ i)
  
instance S.Local PattBuilder where
  local_ i = letPath (S.local_ i)
  
instance S.Field PattBuilder where
  type Compound PattBuilder = P.Vis (PathBuilder Ident) (PathBuilder Key)
  v #. k = letPath (v S.#. k)
  
instance S.VarPath PattBuilder

instance S.Tuple PattBuilder where
  type Tup PattBuilder = UngroupBuilder
  
  tup_ g = ungroup g
  
instance S.Extend PattBuilder where
  type Ext PattBuilder = UngroupBuilder
  
  p # g = p <> ungroup g
  
instance S.Self UngroupBuilder where
  self_ k = matchPun (S.self_ k)
  
instance S.Field UngroupBuilder where
  type Compound UngroupBuilder = P.Vis (PathBuilder Ident) (PathBuilder Key)
  
  p #. k = matchPun (p S.#. k)
  
instance S.Let UngroupBuilder where
  type Lhs UngroupBuilder = PathBuilder Key
  type Rhs UngroupBuilder = PattBuilder
  
  x #= p = UngroupB (intro x) [p]
    
    
-- | Unfold a set of matched fields into a decomposing function
pattdecomp :: S.Path a => M.Map Key (a -> [a]) -> (a -> [a])
pattdecomp = M.foldMapWithKey (\ k f e -> f (e S.#. k))
    
    
-- | Validate a nested group of matched paths are disjoint, and extract
-- a decomposing function
extractdecomp
  :: S.Path a
  => P.Path Key
  --  ^ Path to nested match group
  -> An Key (Maybe (B (a -> [a])))
  -- ^ Group of matched paths to nested patterns
  -> B (Maybe (a -> [a]))
  -- ^ Value decomposition function
extractdecomp _ (An a Nothing) = sequenceA a
extractdecomp p (An a (Just b)) = (B . collect . pure) (OlappedMatch p)
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
  An a (Just as) >>= k = k a <|> (as >>= k)
  Un ma >>= k = Un ((>>= k) <$> ma)
  
 
instance Ord k => MonadFree (M.Map k) (An k) where
  wrap = Un
  

instance Ord k => Alternative (An k) where
  empty = Un M.empty

  An x (Just a) <|> b = (An x . Just) (a <|> b)
  An x Nothing <|> b = An x (Just b)
  a <|> An x Nothing = An x (Just a)
  a <|> An x (Just b) = (An x . Just) (a <|> b)
  Un ma <|> Un mb = Un (M.unionWith (<|>) ma mb)
  
  
instance Ord k => Semigroup (An k a) where
  (<>) = (<|>)
  
  
instance Ord k => Monoid (An k a) where
  mempty = empty
  
  mappend = (<|>)

