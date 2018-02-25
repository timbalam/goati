{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings, FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, FunctionalDependencies #-}
module Expr
  ( expr
  , program
  )
where

import qualified Types.Parser as P
import Types.Expr
import Types.Interpreter( K )
import Util

import Control.Applicative( liftA2, Alternative(..) )
import Control.Monad.Trans( lift )
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable( fold )
import Data.Semigroup
import Data.Monoid( Alt )
import Data.Typeable
import Data.List( elemIndex, nub )
import Data.List.NonEmpty( NonEmpty, toList )
import Data.Void
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S


-- | build executable expression syntax tree
expr
  :: Applicative f
  => P.Expr (P.Name Ident Key a)
  -> f (Expr K (P.Name (Nec Ident) Key a))
expr = go where
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
    :: Applicative f
    => P.Block (P.Expr (P.Name Ident Key a))
    -> f (Defns K (Expr K) (P.Name (Nec Ident) Key a))
  defns' (P.Tup xs) =
    Defns [] <$>
      (M.traverse (checkgetnctx . Pure) . getM) (foldMap (\ x -> setstmt x x) xs)
  defns' (P.Rec xs) = (first P.Priv <$>) <$> rec xs

  
checkgetnctx
  :: P.Path K
  -> Nctx (P.Stmt (P.Expr (P.Name Ident Key P.Import)))
  -> Collect [ScopeErrors] (Node (t (Expr K) (P.Name (Nec Ident) Key P.Import)))
checkgetnctx _ (An a Nothing) = Closed <$> getstmt a
checkgetnctx p (An a (Just b)) = getstmt a *> checkgetnctx p b
  *> (collect . OlappedSet (P.Pub p)) (Tstmt a :| Tstmt <$> toList b)
checkgetnctx p (Un ma) = 
  Open <$> M.traverseWithKey (checkgetnctx . At p) (getM ma)
  
  
extractnctx :: Nctx a -> Node K a
extractnctx n = iternctx (Open . getM) (Closed <$> n)
    

iternctx :: (M K a -> a) -> Nctx a -> a
iternctx _ (An a _) = a
iternctx f (Un fa) = f (iternctx f <$> fa) 


iternctxA :: Alternative p => (M K (p a) -> p a) -> Nctx a -> p a
iternctxA _ (An a Nothing) = pure a
iternctxA f (An a (Just b)) = pure a <|> iternctx f b
iterPnctx f (Un fa) = f (iternctx f <$> fa)


program
  :: Applicative f
  => NonEmpty (P.RecStmt (P.Expr (P.Name Ident Key a)))
  -> f (Defns K (Expr K) (P.Res (Nec Ident) a))
program xs = rec (toList xs)
    

-- | Traverse to find corresponding env and field substitutions
type Nctx = An (M K)
  
  
setstmt
  :: P.Stmt a -> x -> M K (Nctx x)
setstmt = go where
  go (P.Pun p) = setrelpath (public p)
  go (p `P.Set` _) = setrelpath p
  
  setrelpath
    :: P.Path Key -> a -> M K (Nctx a)
  setrelpath p = intro (singletonM . Key <$> p)
  
  
getstmt 
  :: (MonadTrans t, Applicative f)
  => P.Stmt (P.Expr (P.Name Ident Key a))
  -> f (t (Expr K) (P.Name (Nec Ident) Key a))
getstmt = go where
  go (P.Pun p) = lift <$> expr (getpath p)
  go (_ `P.Set` e) = lift <$> expr e
  
  getpath :: P.VarPath -> P.Expr (P.Name Ident Key a)
  getpath = (P.In <$>) . bitraverse go go where
    go :: P.Path a -> P.Expr a
    go p = iter P.Get (P.Var <$> p)

  
public :: Functor f => P.Vis (f Ident) (f Key) -> f Key
public (P.Priv p) = K_ <$> p
public (P.Pub p) = p


intro :: MonadFree (M K) m =>  P.Path (m b -> c) -> b -> c
intro p = iter (\ (f `P.At` k) -> f . wrap . singletonM (Key k)) p . return


type Rctx a = (M Ident a, M K a)


rec
  :: Applicative f
  => [P.RecStmt (P.Expr (P.Name Ident Key a))]
  -> f (Defns K (Expr K) (P.Res (Nec Ident) a))
rec xs = liftA2 (Defns . updateenv ls)
  (traverse f (getM en))
  (traverse f (getM se))
  where
    (en, se) = foldMap (\ x -> setrecstmt x (Right x)) xs
    
    ls = nub (foldMap recstmtctx xs)
    
    
    checkgetnctx
      :: P.Path -> Nctx SomeStmt
      -> Collect [ScopeError] (Node K (Rec K (Expr K) (P.Rec (Nec Ident) a)))
    checkgetnctx _ (An (Rstmt a) Nothing) = 
    
    
    f :: Applicative f
      => Nctx (f (Expr K (P.Name (Nec Ident) Key a)))
      -> f (Node K (Rec K (Expr K) (P.Res (Nec Ident) a)))
    f = (extractnctx <$>) . traverse (abstrec ls <$>)
    
    
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
  :: P.RecStmt a -> x -> Rctx (Nctx x)
setrecstmt = go where
  go (P.DeclVar p) = setvarpath p
  go (l `P.SetRec` _) = setexpr l
  
  
  
setvarpath
  :: P.VarPath -> x -> Rctx (Nctx x)
setvarpath (P.Pub p) x = case t of
  Key (K_ l) -> (singletonM l n, singletonM t n)
  where
    (t, n) = intro ((,) . Key <$> p) x
setvarpath (P.Priv p) x = (singletonM l n, mempty)
  where
    (l, n) = intro ((,) <$> p) x
    
    
setexpr
  :: P.SetExpr -> SomeStmt -> Rctx (Nctx SomeStmt)
setexpr = go where
  go (P.SetPath p) = setvarpath p
  go (P.Decomp stmts) = setdecomp stmts
  go (P.SetDecomp l stmts) = go l <> setdecomp stmts
  
  
  setmatchstmt :: P.Stmt P.SetExpr -> SomeStmt -> Rctx (Nctx SomeStmt)
  setmatchstmt (P.Pun p) = setvarpath p
  setmatchstmt (_ `P.Set` l) = setexpr l
  
  setdecomp :: [P.Stmt P.SetExpr] -> SomeStmt -> Rctx (Nctx SomeStmt)
  setdecomp stmts a = mapuniq a (foldMap (\ x -> setmatchstmt x (Mstmt x)) stmts)
  
  mapuniqrctx
    :: a -> Rctx (Nctx a) -> Rctx (Nctx a)
  mapuniqrctx a = bimap (mapuniqnctx a) (mapuniqnctx a)
  
  mapuniqnctx
    :: a -> Nctx a -> Nctx a
  mapuniqnctx x (An _ Nothing) = An (pure x) Nothing
  mapuniqnctx x a = go a where
    go (An a m) = An a (go <$> m)
    go (Un fa) = Un (mapuniq a <$> fa)
    
  

getrecstmt
  :: P.RecStmt (P.Expr (P.Name Ident Key a))
  -> Collect [ScopeErrors] [Expr K (P.Name (Nec Ident) Key a]
getrecstmt (P.DeclVar p) = (pure . pure . extract) (Var . P.In . P.Pub <$> p) where
  extract :: P.Path (Expr K a) -> Expr K a
  extract = iter (\ (e `P.At` k) -> e `At` Key k)
getrecstmt (l `P.SetRec` e) = getexpr l <*> expr e
  
  
    
getexpr :: P.SetExpr -> Collect [ScopeError] (Expr K a -> [Expr K a])
getexpr = go mempty where
  go m (P.SetPath _) = getdecomp m' <&> (<> pure . rest m') where
    m' = setdecomp m
  go m (P.Decomp stmts) = getdecomp (m <> setdecomp stmts)
  go m (P.SetDecomp l stmts) = go l (m <> setdecomp stmts)
  
    
  rest :: Foldable f => f (Tag k) -> Expr (Tag k) a -> Expr (Tag k) a
  rest ks e = foldl (\ e k -> e `Fix` k) e ks
    
    
  setdecomp
    :: [P.Stmt P.SetExpr]
    -> M K (NonEmpty (Nctx (P.Stmt P.SetExpr)))
  setdecomp stmts = pure <$> foldMap (\ x -> setstmt x x) stmts
  
  
  getdecomp
    :: M K (NonEmpty (Nctx (P.Stmt P.SetExpr)))
    -> Collect [ScopeError] (Expr K a -> [Expr K a])
  getdecomp m =
    M.foldMapWithKey (\ k (f:|fs) e ->
      f e <&> (`At` k)
        <> (fs >>= \ f -> f emptyBlock <&> (`At` k)))
      <$> M.traverseWithKey (checkgetnctxs . Pure) (getM m)
    where
      emptyBlock = Block (Defns [] M.empty)
      
      
  checkgetnctxs
    :: P.Path K
    -> Nctxs (P.Stmt P.SetExpr) -> Collect [ScopeError] (Expr K a -> [Expr K a])
  checkgetnctxs _ (An a Nothing) = getmatchstmt a
  checkgetnctxs p (An a (Just b)) = getmatchstmt a *> checknctxs p b
    *> (collect . pure . OlappedMatch p) (a:toList b)
  checkgetnctxs p (Un ma) =
    M.foldMapWithKey (\ k f e -> f e <&> (`At` k))
      <$> M.traverseWithKey (checkgetnctxs . Free . At p) (get m)
  
  
getmatchstmt
  :: P.Stmt P.SetExpr -> Collect [ScopeErrors] (Expr K a -> [Expr K a])
getmatchstmt (P.Pun p) = pure pure
getmatchstmt (_ `P.Set` l) = getexpr l


recstmt
  :: Applicative f 
  => P.RecStmt (P.Expr (P.Name Ident Key a))
  -> Rctx (Nctx (f (Expr K (P.Name (Nec Ident) Key a))))
recstmt = go where
  go (P.DeclVar p) = declvar p
  go (l `P.SetRec` e) = setexpr l (expr e)
  
  declvar
    :: (Monoid m, Applicative f)
    => P.Path Key -> (M Ident (Nctx (f (Expr K (P.Name a Key b)))), m)
  declvar p = case root p of
    K_ l ->
      ((singletonM l . return . pure . extract) (Var . P.In . P.Pub <$> p), mempty)
  
  
  
setexpr_
  :: Applicative f 
  => P.SetExpr -> f (Expr K (P.Name a Key b))
  -> Rctx (Nctx (f (Expr K (P.Name a Key b))))
setexpr_ = go where
  go (P.SetPath p) = setpath p
  go (P.Decomp stmts) = decomp stmts mempty
  go (P.SetDecomp l stmts) = decomp stmts (setexpr l)
    
    
  decomp
    :: Applicative f
    => [P.Stmt P.SetExpr]
    -> (f (Expr K (P.Name a Key b)) -> Rctx (Nctx (f (Expr K (P.Name a Key b)))))
    -> f (Expr K (P.Name a Key b)) -> Rctx (Nctx (f (Expr K (P.Name a Key b))))
  decomp stmts = (extractdecomp . getM) (foldMap matchstmt stmts)
  
  
  extractdecomp
    :: (Monoid m, Applicative f)
    => M.Map K (Nctx (f (Expr K a) -> m))
    -> (f (Expr K a) -> m)
    -> f (Expr K a) -> m
  extractdecomp m f e = 
    f (rest (M.keys m) <$> e)
      `mappend` extractmap (iternctx (extractmap . getM) <$> m) e
      
  
  extractmap 
    :: (Monoid m, Functor f) 
    => M.Map K (f (Expr K a) -> m)
    -> f (Expr K a) -> m
  extractmap = M.foldMapWithKey (\ k f e -> f (e <&> (`At` k)))
  
    
  rest :: Foldable f => f (Tag k) -> Expr (Tag k) a -> Expr (Tag k) a
  rest ks e = foldl (\ e k -> e `Fix` k) e ks
  
  
  
setpath_
  :: Applicative f
  => P.VarPath -> f (Expr K (P.Name a Key b))
  -> Rctx (Nctx (f (Expr K (P.Name a Key b))))
setpath_ (P.Pub p) e = case t of
  Key (K_ l) -> ((singletonM l . return . pure . Var . P.In . P.Pub) (K_ l), 
    singletonM t n)
  where
    (t, n) = intro ((,) . Key <$> p) e
setpath (P.Priv p) e = (singletonM l n, mempty)
  where
    (l, n) = intro ((,) <$> p) e
    
      
matchstmt_
  :: Applicative f
  => P.Stmt P.SetExpr
  -> M K (Nctx (f (Expr K (P.Name a Key b))
    -> Rctx (Nctx (f (Expr K (P.Name a Key b)))) ))
matchstmt_ = go where
  go (P.Pun p) = matchpun p
  go (p `P.Set` l) = intro (singletonM . Key <$> p) (setexpr l)
  
  matchpun
    :: Applicative f
    => P.VarPath
    -> M K (Nctx (f (Expr K (P.Name a Key b))
      -> Rctx (Nctx (f (Expr K (P.Name a Key b))))))
  matchpun p = intro (singletonM . Key <$> public p) (setpath p)
  

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
  
  
emptyM = Mmap M.empty

singletonM k = Mmap . M.singleton k

traverseMWithKey f = fmap M . M.traverseWithKey f . getM
  
  
instance (Ord k, Alternative f) => Semigroup (M k (f a)) where
  Mmap ma <> Mmap mb = Mmap (M.unionWith (<|>) ma mb)
  
  
instance (Ord k, Alternative f) => Monoid (M k (f a)) where
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


  
-- | Bindings context
data SomeStmt =
    Mstmt (P.Stmt P.SetExpr)
  | Tstmt (P.Stmt (P.Expr (P.Name Ident Key P.Import)))
  | Rstmt (P.RecStmt (P.Expr (P.Name Ident Key P.Import)))


data DefnError =
    OlappedMatch (P.Path K) [P.Stmt P.SetExpr]
  | OlappedSet (P.Path (Vis Ident K)) [SomeStmt]

  
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
  
  


