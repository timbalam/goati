{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses, FunctionalDependencies #-}
module Expr
  ( expr
  , stmt
  , program
  , MonadResolve(..)
  )
where

import qualified Types.Parser as P
import Types.Expr
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
import Data.List( elemIndex )
import Data.List.NonEmpty( NonEmpty, toList )
import Data.Void
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S


-- | build executable expression syntax tree
expr
  :: (Ord k, Applicative f)
  => P.Syntax
  -> f (ExprK k P.VarRes)
expr = go where
  go (P.IntegerLit i) = (pure . Number) (fromInteger i)
  go (P.NumberLit d) = (pure) (Number d)
  go (P.StringLit t) = (pure) (String t) 
  go (P.Var x) = pure (Var x)
  go (P.Get (e `P.At` k)) = liftA2 At (go e) (Key k)
  go (P.Block b) = Block <$> defns' b
  go (P.Extend e b) = liftA2 Update (go e) (defns' b)
  go (P.Unop op e) = go e <&> (`At` Unop op)
  go (P.Binop op e w) = liftA2 updatex (go e <&> (`At` Binop op)) (go w)
    where
      updatex e w =
        (e `Update` (Defns [] . M.singleton (Ident "x") . Closed) (lift w))
          `At` Ident "return"
  
  defns'
    :: (Ord k, Applicative f)
    => P.Block P.Syntax
    -> f (DefnsK k (ExprK k) P.VarRes)
  defns' (P.Tup xs) = defns [] . fold <$> traverse stmt xs
  defns' (P.Rec xs) = (priv <$>) . uncurry defns <$> rec xs where
    priv :: Res a Import -> Res Import (Vis a b)
    priv = (Priv <$>)
  
  
defns
  :: Ord k
  => [Nctx k (Rec k (Expr k) a)]
  -> M k (Nctx k (Rec k (Expr k) a))
  -> Defns k (Expr k) a
defns ectx sctx = Defns (mextract <$> ectx) (mextract <$> getM sctx)
    

-- | Traverse to find corresponding env and field substitutions
type Nctx k = Free (M k)
type NctxK k = Nctx (Tag k)
  
  
stmt 
  :: (Ord k, MonadTrans t, Applicative f)
  => P.Stmt P.Syntax
  -> f (MK k (NctxK k (t (ExprK k) P.VarRes)))
stmt = go where
  go (P.Pun p) = (pure . setstmt (public <$> p)) (exprpath p)
  go (p `P.Set` e) = setstmt p <$> expr e
  
  setstmt
    :: (Ord k, Monad m, MonadTrans t)
    => P.Path Key
    -> m a 
    -> MK k (NctxK k (t m a))
  setstmt p e = intro (singletonm <$> p) (lift e)
  
  exprpath :: (Ord k) => P.VarPath -> ExprK k P.VarRes
  exprpath p = (expr . iter P.Get) (P.Var . In <$> p)

  
public :: Vis Ident Key -> Key
public (Pub t) = t
public (Priv l) = (K_ l)

  
extract :: P.Path (ExprK k a) -> ExprK k a
extract = iter (\ (e `P.At` k) -> e `At` Key k)


type Rctx k a = ([a], M k a)
type RctxK k a = Rctx (Tag k) a


rec
  :: (Ord k, Applicative f)
  => [P.RecStmt P.Syntax]
  -> f (RctxK k (NctxK k (RecK k (ExprK k) (Res Import Ident))))
rec xs = 
  bimap (abstnctx ls <$>) (abstnctx ls <$>)
    <$> (fold <$> traverse recstmt xs)
  where
    ls = recctx xs
    
    abstnctx
      :: (Functor t, Monad n)
      => [Ident]
      -> t (n (Res (Vis Ident k) Import))
      -> t (Rec k n (Res Ident Import))
    abstnctx ls = fmap (abstractRec
      (\ l -> case l of
        Ex a -> Right (Ex a)
        In l -> (maybe . Right) (In l) Left (elemIndex l ls))
      (\ v -> case v of
        Ex a -> Right (Ex a)
        In (Pub t) -> Left t
        In (Priv l) -> Right (In l)))
      
  

recstmt
  :: (Ord k, Applicative f)
  => P.RecStmt P.Syntax
  -> f (RctxK k (NctxK k (ExprK k (VarResK k))))
recstmt = go where
  go (P.DeclVar p) = pure (declvar p)
  go (l `P.SetRec` e) = setexpr l <*> ((tag <$>) <$> expr e)
  
  tag :: Res (Vis a Key) b -> Res (Vis a (Tag k)) b
  tag = first (Key <$>)
  
  
  declvar
    :: (Ord k, Monoid m)
    => P.Path Key
    -> ([NctxK k (ExprK k (VarResK k))], m)
  declvar p =
    ([(Pure . extract) (Var . In . Pub . Key <$> p)], mempty)
  
  
setexpr
  :: (Ord k, Applicative f)
  => P.SetExpr
  -> f (ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
setexpr = go where
  go (P.SetPath p) = pure (setpath p)
  go (P.Decomp stmts) = snd <$> usedecomp stmts
  go (P.SetDecomp l stmts) = liftA2 setdecomp (setexpr l) (usedecomp stmts)
    
  setdecomp
    :: Semigroup m
    => (ExprK k a -> m)
    -> ([Key], ExprK k a -> m)
    -> ExprK k a -> m
  setdecomp f (ks, g) = f . rest <> g where
    rest e = foldl (\ e k -> e `Fix` Key k) e ks
    
  usedecomp
    :: (Ord k, Applicative f)
    => [P.Stmt P.SetExpr]
    -> f ([Key], ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
  usedecomp stmts = fold <$> traverse usematchstmt stmts

  
setpath
  :: Ord k
  => P.VarPath
  -> ExprK k (VarResK k)
  -> RctxK k (NctxK k (ExprK k (VarResK k)))
setpath (Pub p) e = ([(Pure . Var . In) (Pub t)], singletonm t n)
  where
    (t, n) = intro ((,) . Key <$> p) e
setpath (Priv p) e = ([n], emptym)
  where
    (_, n) = intro ((,) <$> p) e
      
        
usematchstmt
  :: (Ord k, Applicative f)
  => P.Stmt P.SetExpr
  -> f ([Key], ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
usematchstmt = go where
  go (P.Pun p) = pure (matchpun p)
  go (p `P.Set` l) = (`useset` p) <$> setexpr l
  
  matchpun
    :: Ord k
    => P.VarPath
    -> ([Key], ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
  matchpun p = useset (setpath p) (public p) where
    public (Pub p) = p
    public (Priv p) = K_ <$> p
  
  useset :: (ExprK k a -> b) -> P.Path Key -> ([Key], ExprK k a -> b)
  useset f p = (f .) <$> useextractrel p
  
  useextractrel :: P.Path Key -> ([Key], ExprK k a -> ExprK k a)
  useextractrel p = ([root p], \ e -> extract (At e . Key <$> p))
  

root :: P.Path b -> b
root = iter (\ (l `P.At` _) -> l)


-- | Traverse to find declared labels
recctx :: [P.RecStmt a] -> [Ident]
recctx = foldMap recstmtctx where
  recstmtctx (P.DeclVar p) = [l] where K_ l = root p
  recstmtctx (l `P.SetRec` _) = setexprctx l
    
  setexprctx :: P.SetExpr -> [Ident]
  setexprctx (P.SetPath p) = pathctx p
  setexprctx (P.Decomp xs) = foldMap matchstmtctx xs
  setexprctx (P.SetDecomp p xs) = setexprctx p <> foldMap matchstmtctx xs
  
  pathctx :: P.VarPath -> [Ident]
  pathctx = maybe [] pure . maybeIdent . bimap root root
  
  matchstmtctx (P.Pun p) = pathctx p
  matchstmtctx (_ `P.Set` l) = setexprctx l

  
maybeIdent (Pub (K_ l)) = Just l
maybeIdent (Priv l) = Just l

  
-- | Bindings context
data DefnError =
    OlappedMatch [P.Stmt P.SetExpr]
  | OlappedSet (P.Block P.Syntax)
  | OlappedVis [Ident]

  
data An f a = An a (An f a) | Un (f (An f a))
  
  
an :: (Semigroup (f (An f a)), Monoid (f (An f a))) => a -> An f a
an a = An a mempty


iterAn :: (Functor f, Semigroup a) => (f a -> a) -> An f a -> a
iterAn f (An a an) = a <> iterAn f an
iterAn f (Un fa) = f (iterAn f <$> fa)


instance Semigroup (f (An f a)) => Semigroup (An f a) where
  An x a <> b = An x (a <> b)
  a <> An x  b = An x (a <> b)
  Un fa <> Un fb = Un (fa <> fb)
    
    
instance (Semigroup (f (An f a)), Monoid (f (An f a))) => Monoid (An f a) where
  mempty = Un mempty
  
  mappend = (<>)
  
  
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

intro :: P.Path (Free (MK k) b -> c) -> b -> c
intro p = iter (\ (f `P.At` k) -> f . Free . singletonm (Key k)) p . Pure

mextract :: Free (M k) a -> Node k a
mextract f = iter (Open . getM) (Closed <$> f)

type MK k = M (Tag k)
  
  


