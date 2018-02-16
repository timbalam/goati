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

  
-- | check for unbound symbols in expression
type Check = Collect (NonEmpty P.Symbol)


-- | Resolve symbols and variables and assign unique ids
class Monad m => MonadResolve k m | m -> k where
  resolveSymbol :: P.Symbol -> m (Key k)
  
  localSymbols :: [P.Symbol] -> m a -> m a
  
  
tag :: MonadResolve k m => P.Tag -> m (Key k)
tag (P.Ident l) = return (Ident l)
tag (P.Symbol s) = resolveSymbol s


var :: MonadResolve k m => P.Var -> m (Vis Ident (Key k))
var = bitraverse pure tag


-- | build executable expression syntax tree

expr
  :: (Ord k, MonadResolve k m)
  => P.Syntax
  -> m (ExprK k P.VarRes)
expr = go where
  go (P.IntegerLit i) = (return . Number) (fromInteger i)
  go (P.NumberLit d) = (return) (Number d)
  go (P.StringLit t) = (return) (String t) 
  go (P.Var x) = return (Var x)
  go (P.Get (e `P.At` x)) = liftA2 At (go e) (tag x)
  go (P.Block b) = Block <$> defns' b
  go (P.Extend e b) = liftA2 Update (go e) (defns' b)
  go (P.Unop op e) = go e <&> (`At` Unop op)
  go (P.Binop op e w) = liftA2 updatex (go e <&> (`At` Binop op)) (go w)
    where
      updatex e w =
        (e `Update` (Defns [] . M.singleton (Ident "x") . Closed) (lift w))
          `At` Ident "return"
  
  defns'
    :: (Ord k, MonadResolve k m)
    => P.Block P.Tag P.Syntax
    -> m (DefnsK k (ExprK k) P.VarRes)
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


data Program k a b = Program (Maybe a) (Defns k (Expr k) b)
  deriving (Functor, Foldable, Traversable)
  
  
instance Ord k => Bifunctor (Program k) where
  bimap = bimapDefault
  
instance Ord k => Bifoldable (Program k) where
  bifoldMap = bifoldMapDefault
  
instance Ord k => Bitraversable (Program k) where
  bitraverse f g (Program m b) = liftA2 Program (traverse f m) (traverse g b)

      
program
  :: (Ord k, MonadResolve k m)
  => P.Program
  -> m (Program k Import (Res Import Ident))
program (P.Program m l) = (,) m . uncurry defns <$> rec (toList l)
    

-- | Traverse to find corresponding env and field substitutions
type Nctx k = Free (M k)
type NctxK k = Nctx (Key k)
  
  
stmt 
  :: (Ord k, MonadTrans t, MonadResolve k m)
  => P.Stmt P.Tag P.Syntax
  -> m (MK k (NctxK k (t (ExprK k) P.VarRes)))
stmt = go where
  go (P.Pun p) = liftA2 (setstmt . fmap public) (varpath p) (exprpath p)
  go (p `P.Set` e) = liftA2 setstmt (relpath p) (expr e)
    
  setstmt
    :: (Ord k, Monad m, MonadTrans t)
    => P.Path (Key k) (Key k)
    -> m a 
    -> MK k (NctxK k (t m a))
  setstmt p e = intro (singletonm <$> p) (lift e)
  
  exprpath :: (Ord k, MonadResolve k m) => P.VarPath -> m (ExprK k P.VarRes)
  exprpath p = (expr . iter P.Get) (P.Var . In <$> p)
    
  
varpath :: MonadResolve k m => P.VarPath -> m (P.Path (Key k) (VarK k))
varpath = bitraverseFree tag var
  

relpath :: MonadResolve k m => P.RelPath -> m (P.Path (Key k) (Key k))
relpath = bitraverseFree tag tag

  
public :: Vis Ident (Key k) -> (Key k)
public (Pub t) = t
public (Priv l) = (Ident l)

  
extract :: P.Path k (Expr k a) -> Expr k a
extract = iter (\ (e `P.At` t) -> e `At` t)


type Rctx k a = ([a], M k a)
type RctxK k a = Rctx (Key k) a


rec
  :: (Ord k, MonadResolve k m)
  => [P.RecStmt P.Tag P.Syntax]
  -> m (RctxK k (NctxK k (RecK k (ExprK k) (Res Import Ident))))
rec xs = 
  bimap (abstnctx ls <$>) (abstnctx ls <$>)
    <$> localSymbols ss (fold <$> traverse recstmt xs)
  where
    (ss, ls) = recctx xs
    
    abstnctx
      :: (Functor t, Monad n)
      => [Ident]
      -> t (n (Res Import (Vis Ident k)))
      -> t (Rec k n (Res Import Ident))
    abstnctx ls = fmap (abstractRec
      (\ l -> case l of
        Ex a -> Right (Ex a)
        In l -> (maybe . Right) (In l) Left (elemIndex l ls))
      (\ v -> case v of
        Ex a -> Right (Ex a)
        In (Pub t) -> Left t
        In (Priv l) -> Right (In l)))
      
  

recstmt
  :: (Ord k, MonadResolve k m)
  => P.RecStmt P.Tag P.Syntax
  -> m (RctxK k (NctxK k (ExprK k (VarResK k))))
recstmt = go where
  go (P.DeclSym _) = return mempty
  go (P.DeclVar l) = declvar <$> relpath (P.Ident <$> l)
  go (l `P.SetRec` e) = setexpr l <*> (expr e >>= tagexpr)
  
  
  tagexpr :: (Traversable t, MonadResolve k m) => t P.VarRes -> m (t (VarResK k))
  -- (traverseExpr . traverseRes) (traverseVis tag)
  tagexpr = (traverse . traverse) (traverse tag)
  
  
  declvar
    :: (Ord k, Monoid m)
    => P.Path (Key k) (Key k)
    -> ([NctxK k (ExprK k (VarResK k))], m)
  declvar p =
    ([(Pure . extract) (Var . In . Pub <$> p)], mempty)
  
  
setexpr
  :: (Ord k, MonadResolve k m)
  => P.SetExpr P.Tag
  -> m (ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
setexpr = go where
  go (P.SetPath p) = setpath <$> varpath p
  go (P.Decomp stmts) = snd <$> usedecomp stmts
  go (P.SetDecomp l stmts) = liftA2 setdecomp (setexpr l) (usedecomp stmts)
    
  setdecomp
    :: Semigroup m
    => (Expr k a -> m)
    -> ([k], Expr k a -> m)
    -> Expr k a -> m
  setdecomp f (ks, g) = f . rest <> g where
    rest = flip (foldl Fix) ks
    
  usedecomp
    :: (Ord k, MonadResolve k m)
    => [P.Stmt P.Tag (P.SetExpr P.Tag)]
    -> m ([Key k], ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
  usedecomp stmts = fold <$> traverse usematchstmt stmts

  
setpath
  :: Ord k
  => P.Path (Key k) (VarK k)
  -> ExprK k (VarResK k)
  -> RctxK k (NctxK k (ExprK k (VarResK k)))
setpath p e = case k of
  Pub t@(Ident _) ->  ([(Pure . Var) (In k)], singletonm t n)
  Pub t -> ([], singletonm t n)
  Priv _ -> ([n], emptym)
  where
    (k, n) = intro ((,) <$> p) e
      
        
usematchstmt
  :: (Ord k, MonadResolve k m)
  => P.Stmt P.Tag (P.SetExpr P.Tag) 
  -> m ([Key k], ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
usematchstmt = go where
  go (P.Pun p) = matchpun <$> varpath p
  go (p `P.Set` l) = liftA2 useset (setexpr l) (relpath p)
  
  matchpun
    :: Ord k
    => P.Path (Key k) (Vis Ident (Key k))
    -> ([Key k], ExprK k (VarResK k) -> RctxK k (NctxK k (ExprK k (VarResK k))))
  matchpun p = useset (setpath p) (public <$> p)
  
  useset :: (Expr k a -> b) -> P.Path k k -> ([k], Expr k a -> b)
  useset f p = (f .) <$> useextractrel p
  
  useextractrel :: P.Path k k -> ([k], Expr k a -> Expr k a)
  useextractrel p = ([root p], extract . (<$> p) . At)
  

root :: P.Path a b -> b
root = iter (\ (l `P.At` _) -> l)


-- | Traverse to find symbols and declared labels
recctx :: [P.RecStmt P.Tag a] -> ([P.Symbol], [Ident])
recctx = foldMap recstmtctx where
  recstmtctx (P.DeclSym s) = ([s], [])
  recstmtctx (P.DeclVar l) = ([], [root l])
  recstmtctx (l `P.SetRec` _) = ([], setexprctx l)
    
  setexprctx :: P.SetExpr P.Tag -> [Ident]
  setexprctx (P.SetPath p) = pathctx p
  setexprctx (P.Decomp xs) = foldMap matchstmtctx xs
  setexprctx (P.SetDecomp p xs) = setexprctx p <> foldMap matchstmtctx xs
  
  pathctx :: P.VarPath -> [Ident]
  pathctx = maybe [] pure . maybeIdent . root
  
  matchstmtctx (P.Pun p) = pathctx p
  matchstmtctx (_ `P.Set` l) = setexprctx l

  
maybeIdent (Pub (P.Ident l)) = Just l
maybeIdent (Pub (P.Symbol _)) = Nothing
maybeIdent (Priv l) = Just l

  
-- | Bindings context
data DefnError =
    OlappedMatch [P.Stmt P.Tag (P.SetExpr P.Tag)]
  | OlappedSet (P.Block P.Tag P.Syntax)
  | OlappedVis [Ident]
  | OlappedSyms [P.Symbol]

  
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

intro :: P.Path k (Free (M k) b -> c) -> b -> c
intro p = iter (\ (f `P.At` t) -> f . Free . singletonm t) p . Pure

mextract :: Free (M k) a -> Node k a
mextract f = iter (Open . getM) (Closed <$> f)

type MK k = M (Key k)
  
  


