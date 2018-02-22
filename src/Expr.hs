{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses, FunctionalDependencies #-}
module Expr
  ( expr
  , program
  )
where

import qualified Types.Parser as P
import Types.Expr
import Types.Interpreter( K )
import Util

import Control.Applicative( liftA2, (<|>) )
import Control.Monad.Trans( lift )
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable( fold )
--import Data.Maybe( fromMaybe )
import Data.Semigroup
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
  :: P.Expr (P.Name Ident Key a) -> Expr K (P.Name (Nec Ident) Key a)
expr = go where
  go (P.IntegerLit i) = Number (fromInteger i)
  go (P.NumberLit d) = Number d
  go (P.StringLit t) = String t
  go (P.Var x) = Var ((first . first) (Nec Req) x)
  go (P.Get (e `P.At` k)) = go e `At` Key k
  go (P.Block b) = Block (defns' b)
  go (P.Extend e b) = go e `Update` defns' b
  go (P.Unop op e) = go e `At` Unop op
  go (P.Binop op e w) = updatex (go e `At` Binop op) (go w)
    where
      updatex e w =
        (e `Update` (Defns [] . (M.singleton . Key) (K_ "x") . Closed) (lift w))
          `At` Key (K_ "return")
  
  defns'
    :: P.Block (P.Expr (P.Name Ident Key a))
    -> Defns K (Expr K) (P.Name (Nec Ident) Key a)
  defns' (P.Tup xs) = (Defns [] . fmap mextract . getM) (foldMap stmt xs)
  defns' (P.Rec xs) = first P.Priv <$> rec xs


program
  :: NonEmpty (P.RecStmt (P.Expr (P.Name Ident Key a)))
  -> Defns K (Expr K) (P.Res (Nec Ident) a)
program xs = rec (toList xs)
    

-- | Traverse to find corresponding env and field substitutions
type Nctx = Free (M K)
  
  
stmt 
  :: (MonadTrans t)
  => P.Stmt (P.Expr (P.Name Ident Key a))
  -> M K (Nctx (t (Expr K) (P.Name (Nec Ident) Key a)))
stmt = go where
  go (P.Pun p) = (setstmt (public p) . expr) (path p)
  go (p `P.Set` e) = setstmt p (expr e)
  
  setstmt
    :: (Monad m, MonadTrans t)
    => P.Path Key
    -> m a
    -> M K (Nctx (t m a))
  setstmt p e = intro (singletonm . Key <$> p) (lift e)
  
  path :: P.VarPath -> P.Expr (P.Name Ident Key a)
  path = (P.In <$>) . bitraverse go go where
    go :: P.Path a -> P.Expr a
    go p = iter P.Get (P.Var <$> p)

  
public :: Functor f => P.Vis (f Ident) (f Key) -> f Key
public (P.Priv p) = K_ <$> p
public (P.Pub p) = p

  
extract :: P.Path (Expr K a) -> Expr K a
extract = iter (\ (e `P.At` k) -> e `At` Key k)


type Rctx a = (M Ident a, M K a)


rec
  :: [P.RecStmt (P.Expr (P.Name Ident Key a))]
  -> Defns K (Expr K) (P.Res (Nec Ident) a)
rec xs = (Defns . updateenv) (f <$> getM en) (f <$> getM se)
  where
    (en, se) = foldMap recstmt xs
    
    f :: Nctx (Expr K (P.Name (Nec Ident) Key a))
      -> Node K (Rec K (Expr K) (P.Res (Nec Ident) a))
    f = mextract . (fmap . abstrec . M.keys) (getM en)
    
    
updateenv
  :: M.Map Ident (Node K (Rec K (Expr K) (P.Res (Nec Ident) a)))
  -> [Node K (Rec K (Expr K) (P.Res (Nec Ident) a))]
updateenv = M.elems . M.mapWithKey (\ k n -> case n of
  Closed _ -> n
  Open fa -> (Closed . wrap
    . (Update . unwrap . return . P.In) (Nec Opt k)
    . Defns []) ((lift . unwrap <$>) <$> fa))
  where
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


recstmt
  :: P.RecStmt (P.Expr (P.Name Ident Key a))
  -> Rctx (Nctx (Expr K (P.Name (Nec Ident) Key a)))
recstmt = go where
  go (P.DeclVar p) = declvar p
  go (l `P.SetRec` e) = setexpr l (expr e)
  
  
  declvar
    :: (Monoid m) => P.Path Key -> (M Ident (Nctx (Expr K (P.Name a Key b))), m)
  declvar p = case root p of
    K_ l ->
      ((singletonm l . Pure . extract) (Var . P.In . P.Pub <$> p), mempty)

  
setexpr
  :: P.SetExpr -> Expr K (P.Name a Key b) -> Rctx (Nctx (Expr K (P.Name a Key b)))
setexpr = go where
  go (P.SetPath p) = setpath p
  go (P.Decomp stmts) = snd (usedecomp stmts)
  go (P.SetDecomp l stmts) = setexpr l `setdecomp` usedecomp stmts
    
  setdecomp
    :: (Semigroup m)
    => (Expr (Tag k) a -> m)
    -> ([Key], Expr (Tag k) a -> m)
    -> Expr (Tag k) a -> m
  setdecomp f (ks, g) = f . rest <> g where
    rest e = foldl (\ e k -> e `Fix` Key k) e (nub ks)
    
  usedecomp
    :: [P.Stmt P.SetExpr]
    -> ( [Key], Expr K (P.Name a Key b) -> Rctx (Nctx (Expr K (P.Name a Key b))) )
  usedecomp stmts = foldMap usematchstmt stmts
  
  
setpath
  :: P.VarPath -> Expr K (P.Name a Key b) -> Rctx (Nctx (Expr K (P.Name a Key b)))
setpath (P.Pub p) e = case t of
  Key (K_ l) -> ((singletonm l . Pure . Var . P.In . P.Pub) (K_ l), singletonm t n)
  where
    (t, n) = intro ((,) . Key <$> p) e
setpath (P.Priv p) e = (singletonm l n, emptym)
  where
    (l, n) = intro ((,) <$> p) e
    
      
        
usematchstmt
  :: P.Stmt P.SetExpr
  -> ( [Key], Expr K (P.Name a Key b) -> Rctx (Nctx (Expr K (P.Name a Key b))) )
usematchstmt = go where
  go (P.Pun p) = matchpun p
  go (p `P.Set` l) = (setexpr l .) <$> useextractrel p
  
  matchpun
    :: P.VarPath
    -> ( [Key], Expr K (P.Name a Key b) -> Rctx (Nctx (Expr K (P.Name a Key b))) )
  matchpun p = (setpath p .) <$> useextractrel (public p)
  
  useextractrel :: P.Path Key -> ([Key], Expr K a -> Expr K a)
  useextractrel p = ([root p], \ e -> extract (At e . Key <$> p))
  

root :: P.Path b -> b
root = iter (\ (l `P.At` _) -> l)
  
  
-- | Wrapped map with a modified semigroup instance
newtype M k a = M { getM :: M.Map k a }
  deriving (Functor, Foldable, Traversable)
  
  
instance (Semigroup a, Ord k) => Semigroup (M k a) where
  M ma <> M mb = M (M.unionWith (<>) ma mb)
  
  
instance (Semigroup a, Ord k) => Monoid (M k a) where
  mempty = emptym
  
  mappend = (<>)
  
  
instance (Semigroup (M k (Free (M k) a)), Ord k) => Semigroup (Free (M k) a) where
  Free ma <> Free mb = Free (ma <> mb)
  a <> _ = a
  
  
emptym :: M k a
emptym = M M.empty
  
singletonm :: k -> a -> M k a
singletonm k = M . M.singleton k

intro :: P.Path (Free (M K) b -> c) -> b -> c
intro p = iter (\ (f `P.At` k) -> f . Free . singletonm (Key k)) p . Pure

mextract :: Free (M K) a -> Node K a
mextract f = iter (Open . getM) (Closed <$> f)
  
  


