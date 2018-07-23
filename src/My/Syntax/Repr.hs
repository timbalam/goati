{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

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
import Data.Functor.Plus (Plus(..), Alt(..))
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

  
-- | Wrapper for applicative syntax error checking
type E = Sap (Collect [DefnError])
--newtype E a = E (Collect [DefnError] a)
--  deriving (Functor, Applicative)
  
runE :: E a -> Either [DefnError] a
runE (Sap e) = getCollect e

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


-- | Core representation builder
type instance S.Member (E (Open (Tag k) a)) = E (Open (Tag k) a)

instance S.Block (E (Open (Tag k) (P.Vis (Nec Ident) a))) where
  type Rec (E (Open (Tag k) (P.Vis (Nec Ident) a))) =
    BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) b))
  block_ b = fmap P.Priv <$> buildBlock b
  
instance (S.Self a, S.Local a) => S.Tuple (E (Open (Tag k) a)) where
  type Tup (E (Open (Tag k) a)) = TupBuilder (Open (Tag k) a)
  tup_ b = Defn . fmap lift <$> buildTup b
  
instance S.Extend (E (Open (Tag k) a)) where
  type Ext (E (Open (Tag k) a)) = E (Open (Tag k) a)
  e # w = liftA2 Update e w
  
type instance S.Member (E (Closed K m a)) = E (m a)
  
instance S.Block (E (Closed K (Open (Tag k)) (Nec Ident))) where
  type Rec (E (Defns K (Open (Tag k)) (Nec Ident))) =
    BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) P.Key))
  block_ = buildBlock
  
type instance S.Member (E (Defns K (Open (Tag k)) (P.Vis (Nec Ident) P.Key))) = 
  E (Open (Tag k) (P.Vis (Nec Ident) P.Key))
  
instance S.Block (E (Defns K (Open (Tag k)) (P.Vis (Nec Ident) P.Key))) where
  type Rec (E (Defns K (Open (Tag k)) (P.Vis (Nec Ident) P.Key))) =
    BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) P.Key))
    
  block_ b = fmap P.Priv <$> buildBlock b
  
instance S.Tuple (E (Defns K (Open (Tag k)) (P.Vis (Nec Ident) P.Key))) where
  type Tup (E (Defns K (Open (Tag k)) (P.Vis (Nec Ident) P.Key))) =
    TupBuilder (Open (Tag k) (P.Vis (Nec Ident) P.Key))
  
  tup_ = buildTup

type instance S.Member (BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) P.Key))) =
  E (Open (Tag k) (P.Vis (Nec Ident) P.Key))

instance S.Deps (BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) P.Key))) where
  prelude_ (BlockB v) b = b' S.#: b
    where
      -- Build a pattern that introduces a local alias for each
      -- component of the imported prelude Block
      b' :: BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) P.Key))
      b' = S.tup_ (foldr puns S.empty_ ns) S.#= S.block_ (BlockB v)
      
      puns :: (S.Splus a, S.Local a) => Ident -> a -> a
      puns i a = S.local_ i S.#: a

      -- identifiers for public component names of prelude Block
      ns = mapMaybe ident (names (selfApp v))
      
      ident :: P.Key -> Maybe Ident
      ident (P.K_ i) = Just i
    
  
  
-- | Build a 'Defns' expression from a parser 'Block' syntax tree.
buildTup :: TupBuilder (E (Open (Tag k) a)) -> E (M.Map Ident (Open (Tag k) a))
buildTup (TupB g xs) = liftA2 substexprs (lnode g) (rexprs xs)
  where
    substexprs se xs = se' where
      se' = M.map f se
      f = (>>=) (xs!!)
  
    -- Right-hand side values to be assigned
    rexprs :: [E a] -> E [a]
    rexprs xs = sequenceA xs
    
    -- Left-hand side paths determine constructed shape
    lnode
      :: Builder Paths -> E (M.Map Ident (Open (Tag k) Int))
    lnode g =
      (E . validate) (build g [0..])
  
    
-- | Validate that a finished tree has unambiguous paths and construct 
--   a 'Node' expression that reflects the tree of assigned values.
--
--   If there are any ambiguous paths, returns them as list of 'OlappedSet'
--   errors.
--
--   Paths with missing values represent paths that must not be assigned
--   and are not included in the constructed 'Node'.
validatePub, validatePriv
  :: Paths a -> Collect [DefnError] (M.Map Ident (Open (Tag k) (Either k a)))
validatePub = validate P.Pub
validatePriv = validate P.Priv

validate
  :: (Path Ident -> P.VarPath) -> Paths a
  -> Collect [DefnError] (M.Map Ident (Open (Tag k) (Either Ident a)))
validate f (Paths m) = M.traverseMaybeWithKey (go pure) m
  where
    go _ _ (An a Nothing) = pure (Var . Right <$> a)
    go g k (An a (Just b)) = (collect . pure . OlappedSet . f) (g k) *> go g k b
    go g k (Un m) =
      Just . Update (Var (Left k)) . Defn . Block
        M.map (fmap Right . superPub . lift)
        <$> M.traverseMaybeWithKey (go (Free . P.At (g k) . K_)) m
        
superPub
  :: Scope Self (Open (Tag k)) (Either Ident a)
  -> Bindings (Open (Tag k)) a
superPub s = Scope (s >>>= f) where
  f :: Monad m => Either Ident a -> Open (Tag k) (Var Super (m a))
  f = either (\ k -> (selfApp . Var) (B_ Super) `At` Key k) (return . F . return)
  
superPriv
  :: Open (Tag k) (Either Ident (Nec Ident))
  -> Open (Tag k) (Nec Ident)
superPriv o = o >>= either (return . Nec Opt) return
        
    
-- | Abstract builder
data Builder group = B_
  { size :: Int
    -- ^ number of values to assign / paths
  , build :: forall a . [a] -> group a
    -- ^ builder function that performs assignment
  , names :: [Ident]
    -- ^ list of top-level names in assignment order
  }
  
instance Alt group => Semigroup (Builder group) where
  B_ sz1 b1 n1 <> B_ sz2 b2 n2 =
    B_ (sz1 + sz2) b (n1 <> n2)
    where
      b :: forall a . [a] -> group a
      b xs = let (x1, x2) = splitAt sz1 xs in b1 x1 <!> b2 x2
  
instance Plus group => Monoid (Builder group) where
  mempty = B_ 0 (const zero) mempty
  mappend = (<>)
  
hoistBuilder :: (forall x . g x -> f x) -> Builder g -> Builder f
hoistBuilder f (B_ sz b n) = B_ sz (f . b) n

    
-- | A 'Path' is a sequence of fields
data Path =
  PathB
    (forall m a . (MonadFree (M.Map Ident) m, Alt m) => m a -> m a)
    -- ^ push additional fields onto path
    Ident
    -- ^ top-level field name

instance S.Self Path where self_ i = PathB id i
  
instance S.Local Path where local_ i = PathB id i
  
instance S.Field Path where
  type Compound Path = Path
  PathB f a #. k = PathB (f . wrap . M.singleton k) a

    
-- | A set of paths
newtype Paths a = Paths
  { unPaths
      :: forall m. (MonadFree (M.Map Ident) m, Alt m)
      => M.Map Ident (m (Maybe a)) 
  }
  
instance Alt Paths where Paths m1 <!> Paths m2 = Paths (M.unionWith (<!>) m1 m2)

instance Plus Paths where zero = Paths M.empty

intro :: Path -> Builder Paths
intro (PathB f n) = B_ 1 (Paths . M.singleton n . f . pure . Just . head) [n]


-- | A punned assignment statement
type Pun = Sbi (,)

-- | A 'Tuple' is a group of paths with associated values
data TupBuilder a =
  TupB
    Builder Paths
    -- ^ constructs tree of fields assigned by statements in a tuple
    [a]
    -- ^ values in assignment order
  
pun :: Pun Path a -> TupBuilder a
pun (Sbi (p, a)) = TupB (intro p) [a]
  
instance S.Self a => S.Self (TupBuilder a) where self_ i = pun (S.self_ i)
  
instance S.Local a => S.Local (TupBuilder a) where local_ i = pun (S.local_ i)
  
instance S.Field a => S.Field (TupBuilder a) where
  type Compound (TupBuilder a) = PunBuilder (S.Compound a)
  b #. k = pun (b S.#. k)
  
instance S.Let (TupBuilder a) where
  type Lhs (TupBuilder a) = Path
  type Rhs (TupBuilder a) = a
  p #= a = TupB (intro p) [a]
    
instance S.Sep (TupBuilder a) where 
  TupB g1 a1 #: TupB g2 a2 = TupB (g1 <> g2) (a1 <> a2)
    
instance S.Splus (TupBuilder a) where
  empty_ = TupB mempty mempty
  
    
-- | Build definitions set from a list of parser recursive statements from
-- a Block.
buildBlock
  :: forall k a . BlockBuilder (Open (Tag k) (P.Vis (Nec Ident) a))
  -> E (Open (Tag k) (Nec Ident))
buildBlock (BlockB g xs) = liftA3 substenv (ldefngroups g) (rexprs xs)
  where
    substenv (en, se) vs = superPriv (Let (map (let_ ls) ds) (let_ ls se')) where
    
      ds :: [Open (Tag k) (Either Ident (Nec Ident))]
      ds = map (\ k -> (Defn . selfApp) (M.findWithDefault (pubAt k) k en')) ls
      
      pubAt :: forall b . Ident -> Bindings (Open (Tag k)) b
      pubAt k = (lift . pub) ((selfApp . Var) (P.Pub Self) `At` Key k)
      
      en' :: M.Map Ident (Bindings (Open (Tag k)) (Either Ident (Nec Ident)))
      en' = M.map (lift . pub . f) en
      
      se' :: Open (Tag k) (Nec Ident)
      se' = (Defn . Block) (M.map (superPub pub . f) se)
      
      f :: forall b. Open (Tag k) (Either b Int)
        -> Open (Tag k) (P.Vis (Either b (Nec Ident)) a)
      f = (>>= either (return . P.Priv . Left) (xs'!!))
      
      xs' :: forall b. [Open (Tag k) (P.Vis (Either b (Nec Ident)) a)]
      xs' = fmap (vis (P.Priv . Right) P.Pub) <$> vs
      
    
    -- Use the source order for private definition list to make predicting
    -- output expressions easier (alternative would be sorted order)
    ls = nub (names g)
    
    rexprs :: forall a . E [a] -> E [a]
    rexprs = id 
    
    ldefngroups
      :: forall k . Builder VisPaths
      -> E 
        ( M.Map Ident (Open (Tag k) (Either Ident Int))
        , M.Map Ident (Open (Tag k) (Either Ident Int))
        )
    ldefngroups g = (E . validatevis . build g) [0..size g]
    
    
-- | Validate that a group of private/public definitions are disjoint, and
--   extract 'Node' expressions for each defined name.
validatevis
  :: VisPaths (Maybe x)
  -> Collect [DefnError]
    ( M.Map Ident (Open (Tag k) (Either Ident x))
    , M.Map Ident (Open (Tag k) (Either Ident x))
    )
validatevis (VisPaths {local=en, selfApp=se}) = viserrs *>
  liftA2 (,) (validatePriv en) (validatePub se)
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    viserrs = M.foldrWithKey
      (\ l (a, b) e -> e *> (collect . pure) (OlappedVis l))
      (pure ())
      (M.intersectionWith (,) en se)

    
-- | Attach optional bindings to the environmental values corresponding to open
--   node definitions, so that private definitions shadow environmental ones on
--   a path basis - e.g. a path declared x.y.z = ... will shadow the .y.z path
--   of any x variable in scope. 
    
   
-- | Abstract a set of private/public bindings in an expression
let_
  :: Monad m
  => [Ident] -> m (Nec Ident) -> Scope Int m (Nec Ident)
let_ ls = abstract
  (\ x@(Nec _ l) -> maybe (Right x) Left (l `elemIndex` ls))
  
pub :: Monad m => m (P.Vis a b) -> Scope Self m a
pub = abstractEither (P.vis Right (const (Left Self)))


-- | Paths partitioned by top-level visibility
newtype VisPaths a = VisPaths { local :: Paths a, self :: Paths a }

instance Alt VisPaths where
  VisPaths l1 s1 <!> VisPaths l2 s2 = VisPaths (l1 <!> l2) (s1 <!> s2)

instance Plus VisPaths where
  zero = VisPaths zero zero
    
introVis :: P.Vis Path Path -> Builder VisPaths
introVis (P.Priv p) = hoistBuilder (\ b -> zero {local = b}) (intro p)
introVis (P.Pub p) = hoistBuilder (\ b -> zero {selfApp = b}) (intro p)

    
-- | A 'Pattern' is a value deconstructor and a group of paths to assign
data PattBuilder =
  PattB
    Builder VisPaths
    (forall k a . E (Open (Tag k) a -> [Open (Tag k) a]))

-- | An ungroup pattern
data Ungroup =
  Ungroup
    PattBuilder
    -- ^ Builds the set of local and public assignments made by rhs patterns, where
    -- assigned values are obtained by deconstructing an original value
    [Ident]
    -- ^ List of fields of the original value used to obtain deconstructed values    
    
letpath :: P.Vis Path Path -> PattBuilder
letpath p = PattB (introVis p) (pure pure)

letungroup :: PattBuilder -> Ungroup -> PattBuilder
letungroup (PattB g1 v1) (Ungroup (PattB g2 v2) n) =
  PattB (g1 <> g2) (v1' <> v2)
    where
      v1'
        :: forall k a . E (Open (Tag k) a -> [Open (Tag k) a])
      v1' = fmap rest <$> v1
      
      rest :: (Open (Tag k) a -> b) -> Open (Tag k) a -> b
      rest f e = (f . Defn . fmap lift . hide (nub n)) (selfApp e)

      -- | Folds over a value to find keys to restrict for an expression.
      --
      -- Can be used as function to construct an expression of the 'left-over' components
      -- assigned to nested ungroup patterns.
      hide :: Foldable f => f Ident -> Closed (Tag k) a -> Closed (Tag k) a
      hide ks e = foldl (\ e k -> e `Fix` Key k) e ks
    
ungroup :: TupBuilder PattBuilder -> Ungroup
ungroup (TupB g ps) =
  Ungroup (PattB pg (liftA2 applyDecomp (ldecomp g) pfs)) (names g)
  where
    ldecomp :: Builder Paths -> E (Open (Tag k) a -> [Open (Tag k) a])
    ldecomp g = pattdecomp <$>
      (M.traverseMaybeWithKey (extractdecomp . Pure) . build g . repeat) (pure pure)
  
    applyDecomp :: Monoid b => (a -> [a]) -> [a -> b] -> (a -> b)
    applyDecomp s fs a = fold (zipWith ($) fs (s a))
    
    (pg, pfs) = foldMap (\ (PattB g f) -> (g, pure <$> f)) ps
    
instance Semigroup PattBuilder where
  PattB g1 v1 <> PattB g2 v2 = PattB (g1 <> g2) (v1 <> v2)
  
instance Monoid PattBuilder where
  mempty = PattB mempty mempty
  mappend = (<>)
  
instance S.Self PattBuilder where self_ i = letpath (S.self_ i)
  
instance S.Local PattBuilder where local_ i = letpath (S.local_ i)
  
instance S.Field PattBuilder where
  type Compound PattBuilder = P.Vis Path Path
  v #. k = letpath (v S.#. k)

type instance S.Member PattBuilder = PattBuilder
type instance S.Member Ungroup = PattBuilder

instance S.Tuple PattBuilder where
  type Tup PattBuilder = TupBuilder PattBuilder
  tup_ g = p where Ungroup p _ = ungroup g
  
instance S.Tuple Ungroup where
  type Tup Ungroup = TupBuilder PattBuilder
  tup_ = ungroup
  
instance S.Extend PattBuilder where
  type Ext PattBuilder = Ungroup
  (#) = letungroup
    
-- | Build a recursive Block group
data BlockBuilder a = BlockB (Builder VisPaths) (E [a])

instance Semigroup (BlockBuilder a) where
  BlockB g1 v1 <> BlockB g2 v2 = BlockB (g1 <> g2) (v1 <> v2)
  
instance Monoid (BlockBuilder a) where
  mempty = BlockB mempty mempty
  mappend = (<>)
  
decl :: Path -> BlockBuilder a
decl (PathB f n) = BlockB b (pure [])
    where
      b = B_ {size=0, build=VisPaths p p, names=[n]}
      p = (Paths . M.singleton n . f) (pure Nothing)
    
instance S.Self (BlockBuilder a) where
  self_ k = decl (S.self_ k)
  
instance S.Field (BlockBuilder a) where
  type Compound (BlockBuilder a) = Path
  b #. k = decl (b S.#. k)

instance S.Let (BlockBuilder (Open (Tag k) a)) where
  type Lhs (BlockBuilder (Open (Tag k) a)) = PattBuilder
  type Rhs (BlockBuilder (Open (Tag k) a)) = E (Open (Tag k) a)
  PattB g f #= v = BlockB g (f <*> a)
      
instance S.Sep (BlockBuilder a) where
  BlockB g1 v1 #: BlockB g2 v2 = BlockB (g1 <> g2) (v1 <> v2)
  
instance S.Splus (BlockBuilder a) where
  empty_ = BlockB mempty mempty
    
    
-- | Unfold a set of matched fields into a decomposing function
pattdecomp :: (S.Path a, Monoid b) => M.Map Ident (a -> b) -> (a -> b)
pattdecomp = M.foldMapWithKey (\ k f a -> f (a S.#. k))
    
    
-- | Validate a nested group of matched paths are disjoint, and extract
-- a decomposing function
extractdecomp
  :: (S.Path a, Monoid b)
  => P.Path P.Key
  --  ^ Path to nested match group
  -> An (Maybe (E (a -> b)))
  -- ^ Group of matched paths to nested patterns
  -> E (Maybe (a -> b))
  -- ^ Value decomposition function
extractdecomp _ (An a Nothing) = sequenceA a
extractdecomp p (An a (Just b)) = (E . collect . pure) (OlappedMatch p)
  *> sequenceA a
  *> extractdecomp p b
extractdecomp p (Un ma) = Just . pattdecomp 
  <$> M.traverseMaybeWithKey (extractdecomp . Free . P.At p . K_) ma

  
-- | Tree of paths with one or values contained in leaves and zero or more
--   in internal nodes
--
--   Semigroup and monoid instances defined will union subtrees recursively
--   and accumulate values.
data An a = An a (Maybe (An a)) | Un (M.Map Ident (An a))
  deriving (Functor, Foldable, Traversable)
  
instance Applicative An where
  pure a = An a Nothing
  (<*>) = ap
  
instance Monad An where
  return = pure
  
  An a Nothing >>= k = k a
  An a (Just as) >>= k = k a <!> (as >>= k)
  Un ma >>= k = Un ((>>= k) <$> ma)
  
instance MonadFree (M.Map Ident) An where
  wrap = Un
  
instance Alt An where
  An x (Just a) <!> b = (An x . Just) (a <!> b)
  An x Nothing <!> b = An x (Just b)
  a <!> An x Nothing = An x (Just a)
  a <!> An x (Just b) = (An x . Just) (a <!> b)
  Un ma <!> Un mb = Un (M.unionWith (<!>) ma mb)

