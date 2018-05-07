{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings, FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies, ExistentialQuantification, ScopedTypeVariables #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Expr
  ( expr
  , program
  , DefnError(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Expr
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
  deriving (Functor, Foldable, Applicative)
  
getB :: B a -> Either [DefnError] a
getB (B e) = getCollect e

instance Semigroup a => Semigroup (B a) where
  B a <> B b = B (liftA2 (<>) a b)
  
instance Monoid a => Monoid (B a) where
  mempty = B (pure mempty)
  
  B a `mappend` B b = B (liftA2 mappend a b)
  
instance S.Self a => Self (B a) where
  self_ = pure . S.self_
  
instance S.Local a => Local (B a) where
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
type instance Member (B (Expr K a)) = B (Expr K a)

instance S.Block (B (Expr K a)) where
  type Rec (B (Expr K a)) = L P.RecStmt []
  
  block_ b = Block <$> block b
  
instance S.Tuple (B (Expr K a)) where
  type Tup (B (Expr K a)) = TupBuilder (An Key) (Expr K a)
  
  tup_ b = Block <$> tup b
  
instance S.Extend (B (Expr K a)) where
  type Ext (B (Expr K a)) = B (Defns K (Expr K) a)
  
  (#) = liftA2 Update
  
instance S.Block (B (Defns K (Expr K) a)) where
  type Rec (B (Defns K (Expr K) a)) = L P.RecStmt []
  
  block_ b = (first P.Priv <$>) <$> block (getL b)
  
instance S.Tuple (B (Defns K (Expr K) a)) where
  type Tup (B (Defns K (Expr K) a)) = TupBuilder (An Key) (Expr K a)
  
  tup_ b = tup b

          
-- | Build a 'Defns' expression from a parser 'Block' syntax tree.
tup :: TupBuilder (An Key) (Expr K a) -> B (Defns K (Expr K) a)
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
  

-- | Build a 'Defns' expression from 'RecStmt's as parsed from the top level of
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
data GroupBuilder f i = GroupB
  { size :: Int
  , build :: forall a . [a] -> M.Map i (f (Maybe a))
  , names :: [i]
  }

instance Alt f => Semigroup (GroupBuilder f i) where
  GroupB sz1 b1 n1 <> GroupB sz2 b2 n2 = GroupB (sz1 + sz2) b (n1 <> n2)
  where
    b xs = let (x1, x2) = splitAt sz1 xs in M.unionWith (<!>) (b1 x1) (b2 x2)
  
instance Alt f => Monoid (GroupBuilder i f b) where
  mempty = GroupB 0 mempty mempty
  
  mappend = (<>)
  

-- | Build up a path to assign an 'x'
data PathBuilder f i = PathB (forall a . f a -> M.Map i (f a)) i

intro :: PathBuilder f i -> GroupBuilder f i
intro (PB f n) = GroupB 1 (f . pure . pure . head) [n]

-- | Build a path and value for a punned assignment
data PunBuilder f a = PunB (PathBuilder f Key) a

-- | Build a tuple group
data TupBuilder f a = TupB (GroupBuilder f Key) [B a]
  deriving (Monoid, Semigroup)
  
pun :: PunBuilder f b -> TupBuilder f a
pun (PunB p a) = TupB (intro p) [a]
    
-- class instances
instance Self (PathBuilder f Key) where
  self_ k = PathB (M.singleton k) k
  
instance Local (PathBuilder f Ident) where
  local_ i = PathB (M.singleton i) i
  
instance MonadFree (M.Map Key) f => Field (PathBuilder f i) where
  type Compound (PathBuilder i) = PathBuilder i
  
  PathB f i #. k = PathB (f . wrap . M.singleton k) i
  
instance MonadFree (M.Map Key) f => Path (PathBuilder f i)

instance Self a => Self (PunBuilder f a) where
  self_ k = PunB (self_ k) (self_ k)
  
instance Local a => Local (PunBuilder f a) where
  local_ i = PunB (self_ (K_ i)) (local_ i)

instance (MonadFree (M.Map Key) f, Field a) => Field (PunBuilder f a) where
  type Compound (PunBuilder f a) = PunBuilder f a
  
  PunB f x  #. k = PunB (f #. k) (x #. k)
  
instance (MonadFree (M.Map Key) f, Path a) => Path (PunBuilder f a)

instance Alt f => Monoid (TupBuilder f a) where
  mempty = TupB mempty mempty
  
  TupB g1 a1 `mappend` TupB g2 a2 = TupB (g1 `mappend` g2) (a1 `mappend` a2)

instance Self a => Self (TupBuilder f a) where
  self_ k = pun (self_ k)
  
instance Local a => Local (TupBuilder f a) where
  local_ i = pun (local_ i)
  
instance (MonadFree (M.Map Key) f, Field a) => Field (TupBuilder f a) where
  type Compound (TupBuilder f a) = PunBuilder f (B a)
  
  b #. k = pun (b #. k)
  
instance (MonadFree (M.Map Key) f, Field a) => VarPath (TupBuilder f a)
  
instance Let (TupBuilder f a) where
  type Lhs (TupBuilder f a) = PathBuilder f Key
  type Rhs (TupBuilder f a) = B a
  
  p #= x = TupB (intro p) [x]
  
instance (MonadFree (M.Map Key) f, Alt f) => TupStmt (TupBuilder f a)
  

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
  :: (M Ident (An Key (Maybe x)), M Key (An Key (Maybe x)))
  -> Collect [DefnError] (M.Map Ident (Node K x), M.Map Key (Node K x))
extractdefngroups (Mmap en, Mmap se) = viserrs *> bitraverse
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
data VisBuilder f a = VisB 
  { local :: GroupBuilder f Ident
  , localValues :: a
  , self :: GroupBuilder f Key
  , selfValues :: a
  }
  deriving Functor
  
instance (Alt f, Semigroup a) => Semigroup (VisBuilder f a) where
  VisB l1 lv1 s1 sv1 <> VisB l2 lv2 s2 sv2 =
    VisB (l1 <> l2) (lv1 <> lv2) (s1 <> s2) (sv1 <> sv2)
  
instance (Alt f, Monoid a) => Monoid (VisBuilder f a) where 
  mempty = VisB mempty mempty mempty mempty
  
  VisB l1 lv1 s1 sv1 `mappend` VisB l2 lv2 s2 sv2 =
    VisB (l1 `mappend` l2) (lv1 `mappend` lv2) (s1 `mappend` s2) (sv1 `mappend` sv2)

    
-- | Build a pattern
data PattBuilder f a = PattB (VisBuilder f (a -> [a])) [Key]

letpath :: Vis (PathBuilder f Ident) (PathBuilder f Key) -> PattBuilder f a
letpath (Pub p) = PattB (VisB { self :: intro p, selfValues = pure pure })
letpath (Priv p) = PattB (VisB { local :: intro p, localValues = pure pure })

ungroup :: UngroupBuilder f a -> B (PattBuilder f a)
ungroup (UngroupB g s ps) =
  extractdecomp (build g) <*> (PattB . fmap applySplit s . mergePatt <$> sequenceA ps)
  where
    applySplit :: (a -> [a]) -> [a -> [a]] -> a -> [a]
    applySaplit s fs = zipWith ($) fs . s
    
    mergePatt :: [PattBuilder f a] -> VisBuilder f [a -> [a]]
    mergePatt = foldMap (\ (Patt v _) -> pure <$> v)
  
-- | Build an ungroup path
newtype MatchBuilder f a = MatchB (PathBuilder (An Key) Key) (a -> [a]) (PattBuilder f a)

match :: MatchBuilder a -> UngroupBuilder f a
match (MatchB x s p) = UngroupB (intro x) s [pure p]
  
-- | Build an ungroup pattern
newtype UngroupBuilder f a =
  UngroupB (GroupBuilder (An Key) Key) (a -> [a]) [B (PattBuilder f a)]
  deriving (Semigroup, Monoid)
    
-- | Build a recursive block group
newtype BlockBuilder f a = BlockB (VisBuilder f (B [a]))
  deriving (Semigroup, Monoid)
  
decl :: PathBuilder f Key -> BlockB f a
decl (PathB f n) =
  BlockB (mempty { self :: mempty { build :: (const . f) (pure Nothing), names = [n] } })

-- class instances
instance Self (BlockBuilder f a) where
  self_ k = decl (self_ k)
  
instance (MonadFree (M.Map Key) f) => Field (BlockBuilder f a) where
  type Compound (BlockBuilder f a) = PathBuilder f Key
  
  b #. k = decl (b #. k)
  
instance Let (BlockBuilder f a) where
  type Lhs (BlockBuilder f a) = PattBuilder f a
  type Rhs (BlockBuilder f a) = B a
  
  PattB b #= a = BlockB (VisB
    { local = local b
    , localValues = localValues b <*> a
    , self = self b
    , selfValues = selfValues b <*> a
    })
  
instance (MonadFree (M.Map Key) f, Alt f) => RecStmt (BlockBuilder f a)
    
instance Self (PattBuilder f a) where
  self_ i = letPath (self_ i)
  
instance Local (PattBuilder f a) where
  local_ i = letPath (local_ i)
  
instance MonadFree (M.Map Key) f => Field (PattBuilder f a) where
  type Compound (PattBuilder f a) = Vis (PathBuilder f Ident) (PathBuilder f Key)
  v #. k = letPath (v #. k)
  
instance MonadFree (M.Map Key) f => VarPath (PattBuilder f a)

instance Tuple (B (PattBuilder f a)) where
  type Tup (PattBuilder f a) = UngroupBuilder f a
  
  tup_ g = ungroup g
  
instance Extend (B (PattBuilder a)) where
  type Ext (PattBuilder a) = UngroupBuilder a
  
  p # g = p <> ungroup g
  
instance Field a => Self (MatchBuilder Key a) where
  self_ k = MatchB (self_ k) (a #. k)
  
instance Field a => Field (MatchBuilder Key a) where
  type Compound (MatchBuilder Key a) = MatchBuilder Key a
  
  MatchB p x #. k = MatchB (p #. k) (x #. k)
  
instance Path (MatchBuilder Key a)
  
instance Alt f => Semigroup (UngroupBuilder f a) where
  UngroupB b1 s1 v1 <> UngroupB b2 s2 v2 = UngroupB (b1 <> b2) (s1 <> s2) (v1 <> v2)
  
instance Alt f => Monoid (UngroupBuilder f a) where
  mempty = Ungroup mempty mempty mempty
  
  mappend = (<>)
  
instance Self (UngroupBuilder f a) =
  self_ k = let MatchB p x = self_ k in
    UngroupB (mempty { build = f . pure . pure . head, n
  
instance Let (UngroupBuilder f a) where
  type Lhs (UngroupBuilder f a) = MatchBuilder Key a
  type Rhs (UngroupBuilder f a) = PattBuilder f a
  
  MatchB (PathB f n) x  #= p =
    UngroupB
      (mempty { build = f . pure . pure . head, names = [n] }) 
      x
      [p]
    
    
-- | Given a parser pattern statement, returns a value that operates on a list
--   of values '[x]' to generate public/private partitioned groups of paths to
--   the input 'x's .
--
--   As with 'recstmtpaths', we use a 'State' type to assign values in source
--   order.
pattpaths
  :: P.Patt -> State [x] (VisGroups (PathGroup (Maybe x)))
pattpaths = go where
  go (P.LetPath p) = varpath p . Just <$> pop
  go (P.Ungroup stmts) = destrucpaths stmts
  go (P.LetUngroup l stmts) = liftA2 (<>) (go l) (destrucpaths stmts)
  
  destrucpaths :: [P.Stmt P.Patt] -> State [x] (VisGroups (PathGroup (Maybe x)))
  destrucpaths stmts = fold <$> traverse matchpaths stmts
  
  matchpaths :: P.Stmt P.Patt -> State [x] (VisGroups (PathGroup (Maybe x)))
  matchpaths (P.Pun p) = varpath p . Just <$> pop
  matchpaths (_ `P.Let` l) = pattpaths l
    
   
-- | Given a parser pattern, generates a value decomposing function.
pattdecomp
  :: P.Patt
  -> Collect [DefnError]
    (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
pattdecomp = go mempty where

  -- | Given an accumulated group of paths to nested patterns over
  --   a chain of destructure+let patterns and a pattern, extracts the final
  --   value decomposition function
  go
    :: M Key (NonEmpty (PathGroup (P.Stmt P.Patt)))
    -- ^ Set of names matched by nested destructuring declarations
    -> P.Patt
    -- ^ Pattern to match
    -> Collect [DefnError]
      (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
    -- ^ Value decomposing function
  go m (P.LetPath p) = (pure . (rest . M.keysSet) (getM m) <>)
    <$> extractdecompchain m
  go m (P.Ungroup stmts) = extractdecompchain (m <> destrucmatches stmts)
  go m (P.LetUngroup l stmts) = go (m <> destrucmatches stmts) l
  
    
  -- | Folds over a value to find keys to restrict for an expression.
  --
  --   Can be used to generate a decomposition function for the 'left-over'
  --   components assigned to a final let path pattern.
  rest :: Foldable f => f Key -> Expr (Tag k) a -> Expr (Tag k) a
  rest ks e = foldl (\ e k -> e `Fix` Key k) e ks
    
    
-- | Build a group of paths to nested patterns from a list of statements
--   for a destructure pattern.
--
--   Note that we wrap the groups matched for each key that at the top
--   level of a destructure pattern in a 'NonEmpty'. It is incorrect to 
--   match the same top level key in two different destructure declarations - 
--   i.e. matched top level keys do not 'fall-through' to the next pattern
--   in a chain.
destrucmatches
  :: [P.Stmt P.Patt]
  -> M Key (NonEmpty (PathGroup (P.Stmt P.Patt)))
destrucmatches stmts = pure <$> foldMap (\ x -> stmtpath x x) stmts


-- | Validate a group of matched paths for a destructure/let pattern chain
--   and extract a decomposition function
--
--   Currently, if a top level key is matched by multiple destructure 
--   declarations, only the outermost declaration is matched to the input 
--   value. The other declarations are matched to an empty block, resulting
--   in a runtime error. When type checking is implemented this should
--   become a type error.
extractdecompchain
  :: M Key (NonEmpty (PathGroup (P.Stmt P.Patt)))
  -> Collect [DefnError]
    (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
extractdecompchain m =
  M.foldMapWithKey (\ k (f:|fs) e ->
    (f (e `At` Key k) <> foldMap ($ emptyBlock `At` Key k) fs) )
    <$> M.traverseWithKey (traverse . extractdecomp . Pure) (getM m)
  where
    emptyBlock = Block (Defns [] M.empty)
    
    
-- | Validate a nested group of matched paths are disjoint, and extract
--   a decomposing function
extractdecomp
  :: P.Path Key
  --  ^ Path to nested match group
  -> PathGroup (P.Stmt P.Patt)
  -- ^ Group of matched paths to nested patterns
  -> Collect [DefnError]
    (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
  -- ^ Value decomposition function
extractdecomp _ (An a Nothing) = matchdecomp a
extractdecomp p (An a (Just b)) = (collect . pure) (OlappedMatch p)
  *> matchdecomp a
  *> extractdecomp p b
extractdecomp p (Un ma) =
  M.foldMapWithKey (\ k f e -> f (e `At` Key k))
    <$> M.traverseWithKey (extractdecomp . Free . P.At p) (getM ma)


-- | Generates value decomposition function for a destructure pattern statement.
matchdecomp
  :: P.Stmt P.Patt
  -> Collect [DefnError]
    (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
matchdecomp (P.Pun _) = pure pure
matchdecomp (_ `P.Let` l) = pattdecomp l
  
  
  
-- | Wrapped map with modified semigroup instance
newtype M k a = Mmap { getM :: M.Map k a }
  deriving (Functor, Foldable, Traversable)
  
  
empty :: M k a
empty = Mmap M.empty

singleton :: k -> a -> M k a
singleton k = Mmap . M.singleton k

unionWith :: (a -> a -> a) -> M k a -> M k a -> M k a
unionWith f (Mmap a) (Mmap b) = Mmap (M.unionWith f a b)
  
  
instance (Ord k, Semigroup a) => Semigroup (M k a) where
  (<>) = unionWith (<>)
  
  
instance (Ord k, Semigroup a) => Monoid (M k a) where
  mempty = emptyM
  
  mappend = (<>)

  
-- | Tree of paths with one or values contained in leaves and zero or more
--   in internal nodes
--
--   Semigroup and monoid instances defined will union subtrees recursively
--   and accumulate values.
data An k a = An a (Maybe (An k a)) | Un (M k (An k a))
  deriving (Functor, Foldable, Traversable)
  
  
instance Ord k => Applicative (An k) where
  pure a = An a Nothing
  
  (<*>) = ap
  
  
instance Ord k => Monad (An k) where
  return = pure
  
  An a Nothing >>= k = k a
  An a (Just as) >>= k = k a <|> (as >>= k)
  Un ma >>= k = Un ((>>= k) <$> ma)
  
 
instance Ord k => MonadFree (M k) (An k) where
  wrap = Un
  

instance Ord k => Alternative (An k) where
  empty = Un emptyM

  An x (Just a) <|> b = (An x . Just) (a <|> b)
  An x Nothing <|> b = An x (Just b)
  a <|> An x Nothing = An x (Just a)
  a <|> An x (Just b) = (An x . Just) (a <|> b)
  Un ma <|> Un mb = Un (ma <> mb)
  
  
instance Ord k => Semigroup (An k a) where
  (<>) = (<|>)
  
  
instance Ord k => Monoid (An k a) where
  mempty = empty
  
  mappend = (<|>)
  
  
-- | Tree of keys with a value contained at the leaves
--
--   Alternative instance unions subtrees and keeps first leaf value
data F k a = Fpure a | Ffree (M k (F k a))
  deriving (Functor, Foldable, Traversable)
  
instance Ord k => Applicative (F k) where
  pure = Fpure
  
  (<*>) = ap
  
  
instance Ord k => Monad (F k) where
  return = pure
  
  Fpure a >>= f = f a
  Ffree fa >>= f = Ffree ((>>= f) <$> fa)
  
    
instance Ord k => MonadFree (M k) (F k) where
  wrap = Ffree

    
instance Ord k => Alternative (F k) where
  empty = Ffree emptyM

  Ffree ma <|> Ffree mb = Ffree (ma <> mb)
  a <|> _ = a
  

instance Ord k => Semigroup (F k a) where
  (<>) = (<|>)
  
  
instance Ord k => Monoid (F k a) where
  mempty = empty
  
  mappend = (<|>)


