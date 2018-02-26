{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings, FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies, ExistentialQuantification, ScopedTypeVariables #-}
module Expr
  ( expr
  , program
  , DefnError(..)
  )
where

import qualified Types.Parser as P
import Types.Expr
import Types.Classes( MyError(..) )
import Types.Interpreter( K )
import Parser( ShowMy(..) )
import Util

import Control.Applicative( liftA2, liftA3, Alternative(..) )
import Control.Monad.Trans( lift )
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable( fold, toList )
import Data.Semigroup
import Data.Monoid( Alt )
import Data.Typeable
import Data.List( elemIndex, nub )
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Void
import Control.Monad.Free
import Control.Monad.State
--import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S


-- | build executable expression syntax tree
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
  
  defns'
    :: forall a. P.Block (P.Expr (P.Name Ident Key a))
    -> Collect [DefnError] (Defns K (Expr K) (P.Name (Nec Ident) Key a))
  defns' (P.Tup xs) = liftA2 tup' setnode getnode
    where
      tup' n xs = Defns [] (((xs!!) <$>) <$> M.mapKeysMonotonic Key n)
    
      getnode
        :: MonadTrans t
        => Collect [DefnError] [t (Expr K) (P.Name (Nec Ident) Key a)]
      getnode = traverse getstmt xs
      
      setnode :: Collect [DefnError] (M.Map Key (Node K Int))
      setnode = (M.traverseWithKey (checkgetnctx . P.Pub . Pure)
        . getM . fold . flip evalState [0..])
          (traverse (\ x -> setstmt x <$> take1) xs)
  defns' (P.Rec xs) = (first P.Priv <$>) <$> rec xs
  
  
take1 :: State [x] x
take1 = state (\ (x:xs) -> (x, xs))
  
    
checkgetnctx
  :: P.VarPath -> Nctx x -> Collect [DefnError] (Node K x)
checkgetnctx _ (An a Nothing) = pure (Closed a)
checkgetnctx p (An a (Just b)) = 
  (collect . pure . OlappedSet p) (const () <$> a : toList b)
    *> checkgetnctx p b
checkgetnctx p (Un ma) = Open . M.mapKeysMonotonic Key
  <$> M.traverseWithKey
    (\ k -> checkgetnctx (bimap (Free . (`P.At` k)) (Free . (`P.At` k)) p))
    (getM ma)


program
  :: NonEmpty (P.RecStmt (P.Expr (P.Name Ident Key a)))
  -> Either [DefnError] (Defns K (Expr K) (P.Res (Nec Ident) a))
program xs = (getCollect . rec) (toList xs)
    

-- | Traverse to find corresponding env and field substitutions
type Nctx = An (M Key)
  
  
setstmt
  :: P.Stmt a -> x -> M Key (Nctx x)
setstmt = go where
  go (P.Pun p) = setrelpath (public p)
  go (p `P.Set` _) = setrelpath p
  
  setrelpath
    :: P.Path Key -> a -> M Key (Nctx a)
  setrelpath p = intro (singletonM <$> p)
  
  
getstmt 
  :: (MonadTrans t)
  => P.Stmt (P.Expr (P.Name Ident Key a))
  -> Collect [DefnError] (t (Expr K) (P.Name (Nec Ident) Key a))
getstmt = go where
  go (P.Pun p) = (pure . lift) (getpath p) 
  go (_ `P.Set` e) = lift <$> Collect (expr e)
  
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


rec
  :: forall a . [P.RecStmt (P.Expr (P.Name Ident Key a))]
  -> Collect [DefnError] (Defns K (Expr K) (P.Res (Nec Ident) a))
rec xs = liftA2 rec' setnodes getnodes
  where
    rec' (en, se) xs =
      Defns
        (updateenv ls (substnode <$> en))
        (substnode <$> M.mapKeysMonotonic Key se)
      where
        substnode = ((xs!!) <$>)
  
    setnodes :: Collect [DefnError]
      (M.Map Ident (Node K Int), M.Map Key (Node K (Int)))
    setnodes =
      (bitraverse
        (M.traverseWithKey (checkgetnctx . P.Priv . Pure) . getM)
        (M.traverseWithKey (checkgetnctx . P.Pub . Pure) . getM)
        . (fold . flip evalState [0..])) (traverse setrecstmt xs)
    
    getnodes :: Collect [DefnError] [Rec K (Expr K) (P.Res (Nec Ident) a)]
    getnodes = (abstrec ls <$>) . fold <$> traverse getrecstmt xs
    
    ls = nub (foldMap recstmtctx xs)
    
    
updateenv
  :: [Ident]
  -> M.Map Ident (Node K (Rec K (Expr K) (P.Res (Nec Ident) a)))
  -> [Node K (Rec K (Expr K) (P.Res (Nec Ident) a))]
updateenv xs = flip map xs . (M.!) . M.mapWithKey (\ k n -> case n of
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
  -> Expr K (P.Name (Nec Ident) Key a)
  -> Rec K (Expr K) (P.Res (Nec Ident) a)
abstrec ls = abstractRec
  (bitraverse (\ x@(Nec _ l) -> maybe (Right x) Left (l `elemIndex` ls)) pure)
  (bitraverse (\ v -> case v of
    P.Pub k -> Left (Key k)
    P.Priv x -> Right x) pure)
    
    
setrecstmt
  :: P.RecStmt a -> State [x] (Rctx (Nctx x))
setrecstmt = go where
  go (P.DeclVar p) = maybe (pure mempty) (setvarpath . P.Priv) (traverse priv p)
    where
      priv (K_ l) = Just l
  go (l `P.SetRec` _) = setexpr l
  
  
  
setvarpath
  :: P.VarPath -> State [x] (Rctx (Nctx x))
setvarpath = go where
  go (P.Pub p) = do 
    (t, n) <- intro ((,) <$> p) <$> take1
    case t of
      K_ l -> (singletonM l . pure <$> take1) <&> (\ x -> (x, singletonM t n))
  go (P.Priv p) = do
    (l, n) <- intro ((,) <$> p) <$> take1
    return (singletonM l n, mempty)
    
    
setexpr
  :: P.SetExpr -> State [x] (Rctx (Nctx x))
setexpr = go where
  go (P.SetPath p) = setvarpath p
  go (P.Decomp stmts) = setdecomp stmts
  go (P.SetDecomp l stmts) = liftA2 (<>) (go l) (setdecomp stmts)
  
  
  setmatchstmt :: P.Stmt P.SetExpr -> State [x] (Rctx (Nctx x))
  setmatchstmt (P.Pun p) = setvarpath p
  setmatchstmt (_ `P.Set` l) = setexpr l
  
  setdecomp :: [P.Stmt P.SetExpr] -> State [x] (Rctx (Nctx x))
  setdecomp stmts = fold <$> traverse setmatchstmt stmts
  
  mapuniq
    :: Functor f => a -> An f a -> An f a
  mapuniq x (An _ Nothing) = An x Nothing
  mapuniq x a = go a where
    go (An a m) = An a (go <$> m)
    go (Un fa) = Un (mapuniq x <$> fa)
    
  

getrecstmt
  :: P.RecStmt (P.Expr (P.Name Ident Key a))
  -> Collect [DefnError] [Expr K (P.Name (Nec Ident) Key a)]
getrecstmt (P.DeclVar p) = pure (pure l) where 
  l = path (Var . P.In . P.Pub <$> p)
getrecstmt (l `P.SetRec` e) = getexpr l <*> Collect (expr e)


getvarpath :: P.VarPath -> Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)]
getvarpath (P.Pub p) e = e : maybe mempty (pure . path) (traverse priv p) where
  priv (K_ l) = (Just . Var . P.In . P.Pub) (K_ l)
getvarpath (P.Priv p) e = pure e
    
    
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
      (f e <> foldMap ($ emptyBlock) fs) <&> (`At` Key k) )
      <$> M.traverseWithKey (traverse . checkmatchnctx . Pure) (getM m)
    where
      emptyBlock = Block (Defns [] M.empty)
      
      
  checkmatchnctx
    :: P.Path Key
    -> Nctx (P.Stmt P.SetExpr)
    -> Collect [DefnError]
      (Expr K (P.Name a Key b) -> [Expr K (P.Name a Key b)])
  checkmatchnctx _ (An a Nothing) = getmatchstmt a
  checkmatchnctx p (An a (Just b)) = getmatchstmt a *> checkmatchnctx p b
    *> (collect . pure . OlappedMatch p) (const () <$> (a : toList b))
  checkmatchnctx p (Un ma) =
    M.foldMapWithKey (\ k f e -> f e <&> (`At` Key k))
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
recstmtctx :: P.RecStmt a -> [Ident]
recstmtctx (P.DeclVar p) = case root p of K_ l -> [l]
recstmtctx (l `P.SetRec` _) = setexprctx l


setexprctx :: P.SetExpr -> [Ident]
setexprctx (P.SetPath p) = varpathctx p
setexprctx (P.Decomp stmts) = foldMap (snd . matchstmtctx) stmts
setexprctx (P.SetDecomp l stmts) = setexprctx l <> foldMap (snd . matchstmtctx) stmts


varpathctx :: P.VarPath -> [Ident]
varpathctx (P.Priv p) = [root p]
varpathctx (P.Pub p) = case root p of K_ l -> [l]
    
    
matchstmtctx :: P.Stmt P.SetExpr -> ([Key], [Ident])
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
 
  
  
-- | Wrapped free with modified alternative instance
data F f a = Fpure a | Ffree (f (F f a))
  deriving (Functor, Foldable, Traversable)
  
instance Functor f => Applicative (F f) where
  pure = Fpure
  
  (<*>) = ap
  
  
instance Functor f => Monad (F f) where
  return = pure
  
  Fpure a >>= f = f a
  Ffree fa >>= f = Ffree ((>>= f) <$> fa)
  
    
instance Functor f => MonadFree f (F f) where
  wrap = Ffree

    
instance Ord k => Alternative (F (M k)) where
  empty = Ffree emptyM

  Ffree ma <|> Ffree mb = Ffree (ma <> mb)
  a <|> _ = a
  

instance Ord k => Semigroup (F (M k) a) where
  (<>) = (<|>)
  
  
instance Ord k => Monoid (F (M k) a) where
  mempty = empty
  
  mappend = (<|>)


  
-- | Bindings context
type Cause = ()

data DefnError =
    OlappedMatch (P.Path Key) [Cause]
  | OlappedSet P.VarPath [Cause]
  deriving (Show, Typeable)
  
  
instance MyError DefnError where
  displayError (OlappedMatch p _) = "Ambiguous destructuring of path " ++ showMy p
  displayError (OlappedSet p _) = "Ambiguous assignment to path " ++ showMy p

  
data An f a = An a (Maybe (An f a)) | Un (f (An f a))
  deriving (Functor, Foldable, Traversable)
  
  
instance Ord k => Applicative (An (M k)) where
  pure a = An a Nothing
  
  (<*>) = ap
  
  
instance Ord k => Monad (An (M k)) where
  return = pure
  
  An a Nothing >>= k = k a
  An a (Just as) >>= k = k a <|> (as >>= k)
  Un ma >>= k = Un ((>>= k) <$> ma)
  
 
instance Ord k => MonadFree (M k) (An (M k)) where
  wrap = Un
  

instance Ord k => Alternative (An (M k)) where
  empty = Un emptyM

  An x (Just a) <|> b = (An x . Just) (a <|> b)
  An x Nothing <|> b = An x (Just b)
  a <|> An x Nothing = An x (Just a)
  a <|> An x (Just b) = (An x . Just) (a <|> b)
  Un ma <|> Un mb = Un (ma <> mb)
  
  
instance Ord k => Semigroup (An (M k) a) where
  (<>) = (<|>)
  
  
instance Ord k => Monoid (An (M k) a) where
  mempty = empty
  
  mappend = (<|>)
  
  


