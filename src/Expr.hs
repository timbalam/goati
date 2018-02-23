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
  defns' (P.Tup xs) = Defns [] <$> (traverse (sequenceA . extractnctx)
    . getM) (foldMap stmt xs)
  defns' (P.Rec xs) = (first P.Priv <$>) <$> rec xs
  
  
extractnctx :: Nctx a -> Node K a
extractnctx n = iternctx (Open . getM) (Closed <$> n)
      

iternctx :: (M K a -> a) -> Nctx a -> a
iternctx _ (An a _) = a
iternctx f (Un fa) = f (iternctx f <$> fa)


program
  :: Applicative f
  => NonEmpty (P.RecStmt (P.Expr (P.Name Ident Key a)))
  -> f (Defns K (Expr K) (P.Res (Nec Ident) a))
program xs = rec (toList xs)
    

-- | Traverse to find corresponding env and field substitutions
type Nctx = An (M K)
  
  
stmt 
  :: (MonadTrans t, Applicative f)
  => P.Stmt (P.Expr (P.Name Ident Key a))
  -> M K (Nctx (f (t (Expr K) (P.Name (Nec Ident) Key a))))
stmt = go where
  go (P.Pun p) = (setstmt (public p) . expr) (path p)
  go (p `P.Set` e) = setstmt p (expr e)
  
  setstmt
    :: (Monad m, MonadTrans t, Functor f)
    => P.Path Key
    -> f (m a)
    -> M K (Nctx (f (t m a)))
  setstmt p e = intro (singletonM . Key <$> p) (lift <$> e)
  
  path :: P.VarPath -> P.Expr (P.Name Ident Key a)
  path = (P.In <$>) . bitraverse go go where
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
    (en, se) = foldMap recstmt xs
    
    ls = nub (foldMap recstmtctx xs)
    
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
  
  extract :: P.Path (Expr K a) -> Expr K a
  extract = iter (\ (e `P.At` k) -> e `At` Key k)
  
  
setexpr
  :: Applicative f 
  => P.SetExpr -> f (Expr K (P.Name a Key b))
  -> Rctx (Nctx (f (Expr K (P.Name a Key b))))
setexpr = go where
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
  
  
  
setpath
  :: Applicative f
  => P.VarPath -> f (Expr K (P.Name a Key b))
  -> Rctx (Nctx (f (Expr K (P.Name a Key b))))
setpath (P.Pub p) e = case t of
  Key (K_ l) -> ((singletonM l . return . pure . Var . P.In . P.Pub) (K_ l), 
    singletonM t n)
  where
    (t, n) = intro ((,) . Key <$> p) e
setpath (P.Priv p) e = (singletonM l n, mempty)
  where
    (l, n) = intro ((,) <$> p) e
    
      
matchstmt
  :: Applicative f
  => P.Stmt P.SetExpr
  -> M K (Nctx (f (Expr K (P.Name a Key b))
    -> Rctx (Nctx (f (Expr K (P.Name a Key b)))) ))
matchstmt = go where
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
data DefnError =
    OlappedMatch [P.Stmt P.SetExpr]
  | OlappedSet (P.Block (P.Expr (P.Name Ident Key P.Import)))

  
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
  
  


