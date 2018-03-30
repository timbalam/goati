{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings, FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies, ExistentialQuantification, ScopedTypeVariables #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression

module My.Expr
  ( expr
  , program
  , DefnError(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Expr
import My.Types.Classes (MyError(..))
import My.Types.Interpreter (K)
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


-- | Build executable expression from a syntax tree
expr
  :: P.Expr (P.Name Ident Key a)
  -> Either [DefnError] (Expr K (P.Name (Nec Ident) Key a))
expr = getCollect . go where
  go (P.IntegerLit i) = (pure . Number) (fromInteger i)
  go (P.NumberLit d) = pure (Number d)
  go (P.StringLit t) = pure (String t)
  go (P.Var x) = (pure . Var) (first (first (Nec Req)) x)
  go (P.Get (e `P.At` k)) = go e <&> (`At` Key k)
  go (P.Block b) = Block <$> defns' b
  go (P.Extend e b) = liftA2 Update (go e) (defns' b)
  go (P.Unop op e) = go e <&> (`At` Unop op)
  go (P.Binop op e w) = liftA2 updatex (go e <&> (`At` Binop op)) (go w)
    where
      updatex e w =
        (e `Update` (Defns [] . (M.singleton . Key) (K_ "x") . Closed) (lift w))
          `At` Key (K_ "return")
  
  -- | Build defintions set from block literal syntax
  defns'
    :: forall a. P.Block (P.Expr (P.Name Ident Key a))
    -> Collect [DefnError] (Defns K (Expr K) (P.Name (Nec Ident) Key a))
  defns' (P.Tup xs) = liftA2 tup' setnode getnode
    where
      tup' n xs = Defns [] (((xs'!!) <$>) <$> M.mapKeysMonotonic Key n)
        where
          xs' = map lift xs
    
      getnode
        :: Collect [DefnError] [Expr K (P.Name (Nec Ident) Key a)]
      getnode = traverse getstmt xs
      
      setnode :: Collect [DefnError] (M.Map Key (Node K Int))
      setnode = (M.traverseMaybeWithKey (checkgetnctx . P.Pub . Pure)
        . getM . fold . flip evalState [0..])
          (traverse (\ x -> setstmt x . Just <$> pop) xs)
  defns' (P.Rec xs) = (first P.Priv <$>) <$> rec xs
  

-- | Build a definition set from top level statements of a file
program
  :: NonEmpty (P.RecStmt (P.Expr (P.Name Ident Key a)))
  -> Either [DefnError] (Defns K (Expr K) (P.Res (Nec Ident) a))
program xs = (getCollect . rec) (toList xs)
  
  
pop :: State [x] x
pop = state (\ (x:xs) -> (x, xs))
    

-- | Alias for a tree of paths having values assigned by a block literal
type Nctx = An Key
  
    
-- | Construct a node if context is a tree of unambiguous paths to values
--
--   If there are any ambiguous paths, returns them as list of 'OlappedSet'
--   errors
--
--   Paths with missing values represent paths that must not be assigned
--   and are dropped from the constructed node
checkgetnctx
  :: P.VarPath
  -- ^ Path to nested context
  -> Nctx (Maybe x)
  -- ^ Nested context
  -> Collect [DefnError] (Maybe (Node K x))
  -- ^ Node from an unambiguous set of paths without missing (Nothing) values
checkgetnctx _ (An a Nothing) = pure (Closed <$> a)
checkgetnctx p (An a (Just b)) = (collect . pure) (OlappedSet p)
    *> checkgetnctx p b
checkgetnctx p (Un ma) = Just . Open . M.mapKeysMonotonic Key
  <$> M.traverseMaybeWithKey
    (\ k -> checkgetnctx (bimap (Free . (`P.At` k)) (Free . (`P.At` k)) p))
    (getM ma)


-- | Generate a tree of paths to a value from a pattern / tuple block statement
setstmt
  :: P.Stmt a -> x -> M Key (Nctx x)
setstmt = go where
  go (P.Pun p) = setrelpath (public p)
  go (p `P.Set` _) = setrelpath p
  
  setrelpath
    :: P.Path Key -> a -> M Key (Nctx a)
  setrelpath p = intro (singletonM <$> p)
  
  
-- | Generate a value from a pattern / tuple block statement
getstmt 
  :: P.Stmt (P.Expr (P.Name Ident Key a))
  -> Collect [DefnError] (Expr K (P.Name (Nec Ident) Key a))
getstmt = go where
  go (P.Pun p) = pure (getpath p) 
  go (_ `P.Set` e) = Collect (expr e)
  
  getpath :: P.VarPath -> Expr K (P.Name (Nec Ident) Key a)
  getpath = (P.In <$>) . bitraverse
    (path . fmap (Var . Nec Req))
    (path . fmap Var)
    

path :: P.Path (Expr K a) -> Expr K a
path = iter (\ (e `P.At` k) -> e `At` Key k)

  
public :: Functor f => P.Vis (f Ident) (f Key) -> f Key
public (P.Priv p) = K_ <$> p
public (P.Pub p) = p


intro :: MonadFree (M Key) m =>  P.Path (m b -> c) -> b -> c
intro p = iter (\ (f `P.At` k) -> f . wrap . singletonM k) p . return


type Rctx a = (M Ident a, M Key a)



  
  
-- Traverse to find corresponding env and field substitutions
rec
  :: forall a . [P.RecStmt (P.Expr (P.Name Ident Key a))]
  -> Collect [DefnError] (Defns K (Expr K) (P.Res (Nec Ident) a))
rec xs = liftA2 rec' setnodes getnodes
  where
    rec' (en, se) xs =
      Defns
        ((flip map ls . (M.!) . updateenv) (substnode <$> en))
        (substnode <$> M.mapKeysMonotonic Key se)
      where
        substnode = ((xs!!) <$>)
  
    setnodes :: Collect [DefnError]
      (M.Map Ident (Node K Int), M.Map Key (Node K Int))
    setnodes = (checkgetrctx . fold) (evalState (traverse setrecstmt xs) [0..])
    
    getnodes :: Collect [DefnError] [Rec K (Expr K) (P.Res (Nec Ident) a)]
    getnodes = (abstrec ls ks <$>) . fold <$> traverse getrecstmt xs
    
    (ls, ks) = bimap nub nub (foldMap recstmtctx xs)
    
    
checkgetrctx
  :: Rctx (Nctx (Maybe x))
  -> Collect [DefnError] (M.Map Ident (Node K x), M.Map Key (Node K x))
checkgetrctx (Mmap en, Mmap se) = viserr comb *> bitraverse
    (M.traverseMaybeWithKey (checkgetnctx . P.Priv . Pure))
    (M.traverseMaybeWithKey (checkgetnctx . P.Pub . Pure))
    (en, se)
  where
    comb = M.intersectionWith (,) en (filterKey se)
    
    viserr = M.foldrWithKey
      (\ l (a, b) e -> e *> (collect . pure) (OlappedVis l))
      (pure ())
    
    filterKey = M.fromAscList
      . mapMaybe (\ (k, a) -> case k of K_ l -> Just (l, a)) . M.toAscList

    
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
    
   
abstrec
  :: [Ident]
  -> [Key]
  -> Expr K (P.Name (Nec Ident) Key a)
  -> Rec K (Expr K) (P.Res (Nec Ident) a)
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
    
    
setrecstmt
  :: P.RecStmt a -> State [x] (Rctx (Nctx (Maybe x)))
setrecstmt = go where
  go (P.DeclVar p) = pure (setvarpath (P.Pub p) Nothing)
  go (l `P.SetRec` _) = setexpr l
  
  
  
setvarpath
  :: P.VarPath -> x -> Rctx (Nctx x)
setvarpath = go where
  go (P.Pub p) x = (mempty, singletonM t n) where
    (t, n) = intro ((,) <$> p) x
  go (P.Priv p) x = (singletonM l n, mempty) where 
    (l, n) = intro ((,) <$> p) x
    
    
setexpr
  :: P.SetExpr -> State [x] (Rctx (Nctx (Maybe x)))
setexpr = go where
  go (P.SetPath p) = setvarpath p . Just <$> pop
  go (P.Decomp stmts) = setdecomp stmts
  go (P.SetDecomp l stmts) = liftA2 (<>) (go l) (setdecomp stmts)
  
  
  setmatchstmt :: P.Stmt P.SetExpr -> State [x] (Rctx (Nctx (Maybe x)))
  setmatchstmt (P.Pun p) = setvarpath p . Just <$> pop
  setmatchstmt (_ `P.Set` l) = setexpr l
  
  setdecomp :: [P.Stmt P.SetExpr] -> State [x] (Rctx (Nctx (Maybe x)))
  setdecomp stmts = fold <$> traverse setmatchstmt stmts
  

getrecstmt
  :: P.RecStmt (P.Expr (P.Name Ident Key a))
  -> Collect [DefnError] [Expr K (P.Name (Nec Ident) Key a)]
getrecstmt (P.DeclVar _) = pure mempty
getrecstmt (l `P.SetRec` e) = getexpr l <*> Collect (expr e)


getvarpath :: P.VarPath -> Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)]
getvarpath _ = pure
    
    
getexpr
  :: P.SetExpr
  -> Collect [DefnError]
    (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
getexpr = go mempty where

  go m (P.SetPath p) = (getvarpath p . (rest . M.keysSet) (getM m) <>)
    <$> getdecomp m
  go m (P.Decomp stmts) = getdecomp (m <> setdecomp stmts)
  go m (P.SetDecomp l stmts) = go (m <> setdecomp stmts) l
  
    
  rest :: Foldable f => f Key -> Expr (Tag k) a -> Expr (Tag k) a
  rest ks e = foldl (\ e k -> e `Fix` Key k) e ks
    
    
  setdecomp
    :: [P.Stmt P.SetExpr]
    -> M Key (NonEmpty (Nctx (P.Stmt P.SetExpr)))
  setdecomp stmts = pure <$> foldMap (\ x -> setstmt x x) stmts
  
  
  getdecomp
    :: M Key (NonEmpty (Nctx (P.Stmt P.SetExpr)))
    -> Collect [DefnError]
      (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
  getdecomp m =
    M.foldMapWithKey (\ k (f:|fs) e ->
      (f (e `At` Key k) <> foldMap ($ emptyBlock `At` Key k) fs) )
      <$> M.traverseWithKey (traverse . checkmatchnctx . Pure) (getM m)
    where
      emptyBlock = Block (Defns [] M.empty)
      
      
  checkmatchnctx
    :: P.Path Key
    -> Nctx (P.Stmt P.SetExpr)
    -> Collect [DefnError]
      (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
  checkmatchnctx _ (An a Nothing) = getmatchstmt a
  checkmatchnctx p (An a (Just b)) = (collect . pure) (OlappedMatch p)
    *> getmatchstmt a
    *> checkmatchnctx p b
  checkmatchnctx p (Un ma) =
    M.foldMapWithKey (\ k f e -> f (e `At` Key k))
      <$> M.traverseWithKey (checkmatchnctx . Free . P.At p) (getM ma)
  
  
getmatchstmt
  :: P.Stmt P.SetExpr
  -> Collect [DefnError]
    (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
getmatchstmt (P.Pun p) = pure (getvarpath p)
getmatchstmt (_ `P.Set` l) = getexpr l


root :: P.Path b -> b
root = iter (\ (l `P.At` _) -> l)


-- | Traverse in order to find identifiers
recstmtctx :: P.RecStmt a -> ([Ident], [Key])
recstmtctx (P.DeclVar p) = ([], [root p])
recstmtctx (l `P.SetRec` _) = setexprctx l


setexprctx :: P.SetExpr -> ([Ident], [Key])
setexprctx (P.SetPath p) = varpathctx p
setexprctx (P.Decomp stmts) = foldMap (snd . matchstmtctx) stmts
setexprctx (P.SetDecomp l stmts) = setexprctx l <> foldMap (snd . matchstmtctx) stmts


varpathctx :: P.VarPath -> ([Ident], [Key])
varpathctx (P.Priv p) = ([root p], [])
varpathctx (P.Pub p) = ([], [root p])
    
    
matchstmtctx :: P.Stmt P.SetExpr -> ([Key], ([Ident], [Key]))
matchstmtctx (P.Pun p) = ([root (public p)], varpathctx p)
matchstmtctx (p `P.Set` l) = ([root p], setexprctx l)
  
  
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


