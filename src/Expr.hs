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
import Data.List( elemIndex )
import Data.List.NonEmpty( NonEmpty, toList )
import Data.Void
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S


-- | Specialised alias for expr variable
data NecType = Req | Opt -- Flag indicating possibly optional binding
data Nec a = Nec NecType a

type VarK = Nec (P.Vis Ident K)


-- | build executable expression syntax tree
expr
  :: (Applicative f) => P.Expr (P.Res P.Var a) -> f (Expr K (P.Res (Nec P.Var) a))
expr = go where
  go (P.IntegerLit i) = (pure . Number) (fromInteger i)
  go (P.NumberLit d) = (pure) (Number d)
  go (P.StringLit t) = (pure) (String t) 
  go (P.Var x) = (pure . Var) (first (Nec Req) x)
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
    :: (Applicative f)
    => P.Block (P.Expr (P.Res P.Var a))
    -> f (Defns K (Expr K) (P.Res P.Var a))
  defns' (P.Tup xs) = defns [] . fold <$> traverse stmt xs
  defns' (P.Rec xs) = (first P.Priv <$>) . uncurry defns <$> rec xs
  
  
defns
  :: [Nctx (Rec K (Expr K) a)]
  -> M (Nctx (Rec K (Expr K) a))
  -> Defns K (Expr K) a
defns ectx sctx = Defns (mextract <$> ectx) (mextract <$> getM sctx)


program
  :: (Applicative f)
  => NonEmpty (P.RecStmt (P.Expr (P.Res P.Var a)))
  -> f (Defns K (Expr K) (P.Res Ident a))
program xs = uncurry defns <$> rec (toList xs)
    

-- | Traverse to find corresponding env and field substitutions
type Nctx = An M
  
  
stmt 
  :: (MonadTrans t, Applicative f)
  => P.Stmt (P.Expr (P.Res P.Var a))
  -> f (M (Nctx (t (Expr K) (P.Res P.Var a))))
stmt = go where
  go (P.Pun p) = setstmt (public p) <$> exprpath p
  go (p `P.Set` e) = setstmt p <$> expr e
  
  setstmt
    :: (Monad m, MonadTrans t)
    => P.Path Key
    -> m a
    -> M (Nctx (t m a))
  setstmt p e = intro (singletonm . Key <$> p) (lift e)
  
  exprpath :: (Applicative f) => P.VarPath -> f (Expr K (P.Res P.Var a))
  exprpath = expr . (In <$>) . bitraverse go go where
    go :: P.Path a -> P.Expr a 
    go p = iter P.Get (P.Var <$> p)

  
public :: Functor f => P.Vis (f Ident) (f Key) -> f Key
public (P.Pub p) = p
public (P.Priv p) = K_  <$> p

  
extract :: P.Path (Expr K a) -> Expr K a
extract = iter (\ (e `P.At` k) -> e `At` Key k)


type Rctx a = ([a], M a)


rec
  :: (Applicative f)
  => [P.RecStmt (P.Expr (P.Res P.Var a))]
  -> f (Rctx (Nctx (Rec K (Expr K) (P.Res Ident a))))
rec xs = 
  bimap (abstnctx ls <$>) (abstnctx ls <$>)
    <$> (fold <$> traverse recstmt xs)
  where
    ls = recctx xs
    
    abstnctx
      :: (Functor t, Monad n)
      => [Ident]
      -> t (n (P.Res (P.Vis Ident k) a))
      -> t (Rec k n (P.Res Ident a))
    abstnctx ls = fmap (abstractRec
      (bitraverse (\ l -> (maybe . Right) l Left (elemIndex l ls)) pure)
      (bitraverse (\ v -> case v of
        P.Pub t -> Left t
        P.Priv l -> Right l) pure))
      
  

recstmt
  :: (Applicative f)
  => P.RecStmt (P.Expr (P.Res P.Var a))
  -> f (Rctx (Nctx (Expr K (P.Res VarK a))))
recstmt = go where
  go (P.DeclVar p) = pure (declvar p)
  go (l `P.SetRec` e) = setexpr l <*> ((tag <$>) <$> expr e)
  
  tag :: P.Res (P.Vis a Key) b -> P.Res (P.Vis a (Tag k)) b
  tag = first (Key <$>)
  
  
  declvar
    :: (Monoid m)
    => P.Path Key
    -> ([Nctx (Expr K (P.Res (P.Vis b K) a))], m)
  declvar p =
    ([(Pure . extract) (Var . In . P.Pub . Key <$> p)], mempty)
  
  
setexpr
  :: (Applicative f)
  => P.SetExpr
  -> f (Expr K (P.Res VarK a) -> Rctx (Nctx (Expr K (P.Res VarK a))))
setexpr = go where
  go (P.SetPath p) = pure (setpath p)
  go (P.Decomp stmts) = snd <$> usedecomp stmts
  go (P.SetDecomp l stmts) = liftA2 setdecomp (setexpr l) (usedecomp stmts)
    
  setdecomp
    :: Semigroup m
    => (Expr (Tag k) a -> m)
    -> ([Key], Expr (Tag k) a -> m)
    -> Expr (Tag k) a -> m
  setdecomp f (ks, g) = f . rest <> g where
    rest e = foldl (\ e k -> e `Fix` Key k) e ks
    
  usedecomp
    :: (Applicative f)
    => [P.Stmt P.SetExpr]
    -> f ([Key], Expr K (P.Res VarK a) -> Rctx (Nctx (Expr K (P.Res VarK a))))
  usedecomp stmts = fold <$> traverse usematchstmt stmts

  
setpath
  :: P.VarPath
  -> Expr K (P.Res VarK a)
  -> Rctx (Nctx (Expr K (P.Res VarK a)))
setpath (P.Pub p) e = ([(Pure . Var . In) (P.Pub t)], singletonm t n)
  where
    (t, n) = intro ((,) . Key <$> p) e
setpath (P.Priv p) e = ([n], emptym)
  where
    (_, n) = intro ((,) <$> p) e
    
      
        
usematchstmt
  :: (Applicative f)
  => P.Stmt P.SetExpr
  -> f ([Key], Expr K (P.Res VarK a) -> Rctx (Nctx (Expr K (P.Res VarK a))))
usematchstmt = go where
  go (P.Pun p) = pure (matchpun p)
  go (p `P.Set` l) = (`useset` p) <$> setexpr l
  
  matchpun
    :: P.VarPath
    -> ([Key], Expr K (P.Res VarK a) -> Rctx (Nctx (Expr K (P.Res VarK a))))
  matchpun p = useset (setpath p) (public p)
  
  useset :: (Expr K a -> b) -> P.Path Key -> ([Key], Expr K a -> b)
  useset f p = (f .) <$> useextractrel p
  
  useextractrel :: P.Path Key -> ([Key], Expr K a -> Expr K a)
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

  
maybeIdent (P.Pub (K_ l)) = Just l
maybeIdent (P.Priv l) = Just l

  
-- | Bindings context
data DefnError =
    OlappedMatch [P.Stmt P.SetExpr]
  | OlappedSet (P.Block (P.Expr (P.Res P.Var Import)))
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
newtype M a = M { getM :: M.Map K a }
  deriving (Functor, Foldable, Traversable)
  
instance (Semigroup a) => Semigroup (M a) where
  M ma <> M mb = M (M.unionWith (<>) ma mb)
  
  
instance (Semigroup a) => Monoid (M a) where
  mempty = emptym
  
  mappend = (<>)
  
  
instance (Semigroup (M (Free M a))) => Semigroup (Free M a) where
  Free ma <> Free mb = Free (ma <> mb)
  a <> _ = a
  
  
emptym :: M a
emptym = M M.empty
  
singletonm :: K -> a -> M a
singletonm k = M . M.singleton k

intro :: P.Path (Free M b -> c) -> b -> c
intro p = iter (\ (f `P.At` k) -> f . Free . singletonm (Key k)) p . Pure

introAn :: P.Path (An M b -> c) -> b -> c
introAn p = iter (\ (f `P.At` k) -> f . Un . singletonm (Key k)) p . an

mextract :: Free M a -> Node K a
mextract f = iter (Open . getM) (Closed <$> f)


anextract :: An M a -> Collect [DefnError] (Node K a)
anextract f = iterAn (Open . getM) (pure . Closed <$> f)
  
  


