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
  type Tup (B (Expr K a)) = L P.Stmt []
  
  tup_ b = Block <$> tup b
  
instance S.Extend (B (Expr K a)) where
  type Ext (B (Expr K a)) = B (Defns K (Expr K) a)
  
  (#) = liftA2 Update
  
instance S.Block (B (Defns K (Expr K) a)) where
  type Rec (B (Defns K (Expr K) a)) = L P.RecStmt []
  
  block_ b = (first P.Priv <$>) <$> block (getL b)
  
instance S.Tuple (B (Defns K (Expr K) a)) where
  type Tup (B (Defns K (Expr K) a)) = TupBuilder
  
  tup_ b = tup b

          
-- | Build a 'Defns' expression from a parser 'Block' syntax tree.
tup
  :: forall a. TupBuilder (B (Expr K (P.Name (Nec Ident) Key a)))
  -> B (Defns K (Expr K) (P.Name (Nec Ident) Key a))
tup (TB b) = liftA2 substexprs (lnode xs) (rexprs xs)
  where
    substexprs nd xs = Defns [] (((xs'!!) <$>) <$> M.mapKeysMonotonic Key nd)
      where
        xs' = map lift xs
  
    -- Right-hand side values to be assigned
    rexprs
      :: GroupBuilder (B (Expr (P.Name (Nec Ident) Key a)))
      -> Collect [DefnError] [Expr K (P.Name (Nec Ident) Key a)]
    rexprs b = traverse values b
    
    -- Left-hand side paths determine constructed shape
    lnode
      :: GroupBuilder (B (Expr (P.Name (Nec Ident) Key a)))
      -> Collect [DefnError] (M.Map Key (Node K Int))
    lnode xs = 
      M.traverseMaybeWithKey (extractnode . P.Pub . Pure) (getM (build b [0..]))
  

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
data GroupBuilder i a b = GB { build :: [a] -> M i (An Key b), values :: [b] }
  deriving Functor

instance Alt (GroupBuilder i a) where
  GB b1 v1 <> GB b2 v2 = GB b (v1 <> v2)
  where
    b xs = let (x1, x2) = splitAt (length v1) xs in b1 x1 <!> b2 x2
  
instance Plus (GroupBuilder i a) where
  zero = GB mempty mempty
  

-- | Build up a path to assign an 'x'
newtype PathBuilder i x = PB (An Key x -> M i (An Key x))

-- | Build a path and value for a punned assignment
data PunBuilder x = PP (PathBuilder Key x) x

-- | Build a tuple group
newtype TupBuilder a b = TB (GroupBuilder Key a b)
  deriving (Alt, Plus)

  
instance Self (PathBuilder Key x) where
  self_ = PB . M . M.singleton
  
instance Local (PathBuilder Ident x) where
  local_ = PB . M . M.singleton
  
instance Field (PathBuilder i x) where
  type Compound (PathBuilder i x) = PathBuilder i x
  
  PB f #. k = PB . f . M . M.singleton k
  
instance Path (PathBuilder i x)

instance Self x => Self (PunBuilder x) where
  self_ k = PP (self_ k) (self_ k)
  
instance Local x => Local (PunBuilder x) where
  local_ i = PP (self_ (K_ i)) (local_ i)

instance Field x => Field (PunBuilder x) where
  type Compound (PunBuilder x) = PunBuilder x
  
  PP f x  #. k = PP (f #. k) (x #. k)
  
instance Path x => Path (PunBuilder x)

instance Self x => Self (TupBuilder i a) where
  self_ k = let PP (PB f) x = self_ k in 
    TB (mempty { build = f . pure head, values = [x]  })
  
instance Local a => Local (TupBuilder i a a) where
  local_ i = let PP (PB f) x = local_ i in 
    TB (mempty { build = f . pure head, values = [x] })
  
instance Field a => Field (TupBuilder i a a) where
  type Compound (GroupBuilder x) = PunBuilder x
  
  b #. k = let PP (PB f) x = b #. k in
    TB (mempty { build = f . pure head, values = [x] })
  
instance VarPath1 (TupBuilder a)
  
instance Let (TupBuilder a) where
  type Lhs (TupBuilder a) = PathBuilder Key a
  
  PB f #= a = TB (mempty { build = f . pure head, values = [a] })
  
instance TupStmt TupBuilder


-- | Alias representing a group of name definitions partitiioned by 
--   public/private visibility
data BlockBuilder x = BB 
  { local :: GroupBuilder Ident x
  , names :: [Ident]
  , self :: GroupBuilder Key x
  }
  

-- | Build definitions set from a list of parser recursive statements from
--   a block.
block
  :: forall a . [P.RecStmt (P.Expr (P.Name Ident Key a))]
  -> Collect [DefnError] (Defns K (Expr K) (P.Res (Nec Ident) a))
block xs = liftA2 substexprs (ldefngroups xs) (rexprs xs)
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
    (ls, ks) = bimap nub nub (foldMap recstmtnames xs)
  
    ldefngroups
      :: [P.RecStmt (P.Expr (P.Name Ident Key a))]
      -> Collect [DefnError]
        (M.Map Ident (Node K Int), M.Map Key (Node K Int))
    ldefngroups xs = (extractdefngroups
      . fold) (evalState (traverse recstmtpaths xs) [0..])
    
    rexprs
      :: [P.RecStmt (P.Expr (P.Name Ident Key a))]
      -> Collect [DefnError] [Expr K (P.Name (Nec Ident) Key a)]
    rexprs xs = fold <$> traverse recstmtexpr xs
    
    
    
-- | Validate that a group of private/public definitions are disjoint, and
--   extract 'Node' expressions for each defined name.
extractdefngroups
  :: VisGroups (PathGroup (Maybe x))
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
    
    
-- | Given a parser recursive statement, returns a value that operates on a list
--   of values to generate public/private partitioned groups of paths to values.
--
--   The 'State' type enforces that values are assigned in source order. It is
--   required that 'recstmtexpr' below generates values in the same order.
recstmtpaths
  :: P.RecStmt a -> State [x] (VisGroups (PathGroup (Maybe x)))
recstmtpaths = go where
  go (P.Decl p) = pure (varpath (P.Pub p) Nothing)
  go (l `P.LetRec` _) = pattpaths l
  
  
  
-- | 'varpath p x' takes a parser path 'p' and a value 'x' and returns a
--   public/private partitioned group of names containing a single path to 'x'.
varpath
  :: P.VarPath -> x -> VisGroups (PathGroup x)
varpath = go where
  go (P.Pub p) x = (mempty, singletonM t n) where
    (t, n) = intro ((,) <$> p) x
  go (P.Priv p) x = (singletonM l n, mempty) where 
    (l, n) = intro ((,) <$> p) x
    
    
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
  

-- | Traverse a list of parser recursive statements and construct a list of
--   core expressions to assign to paths.
--
--   Values should be ordered as expected by 'recstmtpaths' etc.  
recstmtexpr
  :: P.RecStmt (P.Expr (P.Name Ident Key a))
  -> Collect [DefnError] [Expr K (P.Name (Nec Ident) Key a)]
recstmtexpr (P.Decl _) = pure mempty
recstmtexpr (l `P.LetRec` e) = pattdecomp l <*> Collect (expr e)
    
   
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


-- | Get path root.
root :: P.Path b -> b
root = iter (\ (l `P.At` _) -> l)


-- | Traverse in order to find identifiers in source order
recstmtnames :: P.RecStmt a -> ([Ident], [Key])
recstmtnames (P.Decl p) = ([], [root p])
recstmtnames (l `P.LetRec` _) = pattnames l


pattnames :: P.Patt -> ([Ident], [Key])
pattnames (P.LetPath p) = varpathnames p
pattnames (P.Ungroup stmts) = foldMap (snd . stmtnames) stmts
pattnames (P.LetUngroup l stmts) = pattnames l <> foldMap (snd . stmtnames) stmts


varpathnames :: P.VarPath -> ([Ident], [Key])
varpathnames (P.Priv p) = ([root p], [])
varpathnames (P.Pub p) = ([], [root p])
    
    
stmtnames :: P.Stmt P.Patt -> ([Key], ([Ident], [Key]))
stmtnames (P.Pun p) = ([root (public p)], varpathnames p)
stmtnames (p `P.Let` l) = ([root p], pattnames l)
  
  
-- | Wrapped map with modified semigroup instance
newtype M k a = Mmap { getM :: M.Map k a }
  deriving (Functor, Foldable, Traversable)
  
  
emptyM :: M k a
emptyM = Mmap M.empty

singletonM :: k -> a -> M k a
singletonM k = Mmap . M.singleton k
  
  
instance (Ord k, Semigroup a) => Semigroup (M k a) where
  Mmap ma <> Mmap mb = Mmap (M.unionWith (<>) ma mb)
  
  
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


