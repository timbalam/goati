{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings, FlexibleInstances, UndecidableInstances #-}
module Expr
  ( expr
  , stmt
  , rec
  , ScopeError(..)
  , Check
  , Resolve
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
import Data.List.NonEmpty( NonEmpty )
import Data.Void
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Set as S

  
-- | check for free parameters in expression
data ScopeError =
    FreeSym P.Symbol
  | FreeParam Ident
  deriving (Eq, Show, Typeable)
  
  
type Check = Collect [ScopeError]


-- | Resolve symbols and variables and assign unique ids
class Monad m => MonadResolve m where
  resolveSymbol :: P.Symbol -> m (Maybe Key)
  
  localSymbols :: [P.Symbol] -> m a -> m a
  
  
tag :: MonadResolve m => P.Tag -> m (Check Key)
tag (P.Ident l) = (return . pure) (Ident l)
tag (P.Symbol s) = maybe def pure <$> resolveSymbol s where
  def = (collect . pure) (FreeSym s)
  
  
class Monad m => MonadAbstract m where
  abstractIdent :: Ident -> m (Maybe Int)
  
  localIdents :: [Ident] -> m a -> m a
  
  envIdents :: m [Node (Rec Expr (Vis Int a))]
  
  
ident :: MonadAbstract m => Ident -> m (Check Int)
ident x = maybe def pure <$> abstractIdent x where
  def = (collect . pure) (FreeParam x)
 

-- | Concrete instance
data ResolveCtx = ResolveCtx
  { symbols :: M.Map P.Symbol Int
  , bindings :: [Ident]
  }
  
newtype Resolve a = Resolve (StateT Int (Reader ResolveCtx) a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadReader ResolveCtx)

  
new :: (MonadState i m, Enum i) => m i
new = state (\ i -> (succ i, i))


instance MonadResolve Resolve where
  resolveSymbol s = asks ((Symbol <$>) . M.lookup s . symbols)
  
  localSymbols s m = do
    s' <- (sequenceA . M.fromSet (const new)) (S.fromList s)
    local (\ ctx -> ctx { symbols = s' `M.union` symbols ctx }) m
  
  
instance MonadAbstract Resolve where
  abstractIdent l = asks (elemIndex l . bindings) 
  
  localIdents ls =
    local (\ ctx -> ctx { bindings = ls ++ bindings ctx })
    
  envIdents = asks (zipWith (const . mkvar) [0..] . bindings) where
    mkvar = Closed . return . Priv
    

-- | Wrapped map with a modified semigroup instance
newtype M k a = M { getM :: M.Map k a }
  deriving (Functor, Foldable, Traversable)
  
instance (Semigroup a, Ord k) => Semigroup (M k a) where
  M ma <> M mb = M (M.unionWith (<>) ma mb)
  
  
instance (Semigroup a, Ord k) => Monoid (M k a) where
  mempty = M (M.empty)
  
  mappend = (<>)
  
  
instance (Semigroup (M k (Free (M k) a)), Ord k) => Semigroup (Free (M k) a) where
  Free ma <> Free mb = Free (ma <> mb)
  a <> _ = a
  
  
msingleton :: k -> a -> M k a
msingleton k = M . M.singleton k

intro :: P.Path Key (Free (M Key) b -> c) -> b -> c
intro p = iter (\ (f `P.At` t) -> f . Free . msingleton t) p . Pure

mextract :: Free (M Key) a -> Node a
mextract f = iter (Open . getM) (Closed <$> f)

        
type Var' = Vis Int Key


-- | build executable expression syntax tree
expr
  :: (MonadAbstract m, MonadResolve m)
  => P.Syntax
  -> m (Check (Expr Var'))
expr = go where
  go (P.IntegerLit i) = (return . pure . Number) (fromInteger i)
  go (P.NumberLit d) = (return . pure) (Number d)
  go (P.StringLit t) = (return . pure) (String t)
  go (P.Var x) = (Var <$>) <$> var x
  go (P.Get (e `P.At` x)) = liftA2 (liftA2 At) (go e) (tag x)
  go (P.Block b) = block b
  go (P.Extend e b) = liftA2 (liftA2 Update) (go e) (block b)
  go (P.Unop op e) = go e <&> ((`At` Unop op) <$>)
  go (P.Binop op e w) = liftA2 (liftA2 updatex) (go e <&> ((`At` Binop op) <$>)) (go w) where
    updatex e w =
      (e `Update` (Block [] . M.singleton (Ident "x") . Closed) (lift w))
        `At` Ident "return"
  
  var = bitraverse2 ident tag
  
  block (P.Tup xs) = tup xs
  block (P.Rec xs) = rec xs
  
  
tup
  :: (MonadResolve m, MonadAbstract m)
  => [P.Stmt P.Tag P.Syntax]
  -> m (Check (Expr Var'))
tup xs = (tup' . fold <$>) <$> traverse2 stmt xs
  where
    tup' se = Block [] (mextract <$> getM se)
  
  
stmt 
  :: (MonadAbstract m, MonadResolve m)
  => P.Stmt P.Tag P.Syntax
  -> m (Check (M Key (Free (M Key) (Rec Expr Var'))))
stmt = go where
  go (P.Pun p) = (setpun <$>) <$> punpath p
  go (p `P.Set` e) = liftA2 (liftA2 setstmt) (relpath p) (expr e)
      
  setpun
    :: P.Path Key (Vis (Ident, Int) Key)
    -> M Key (Free (M Key) (Rec Expr (Vis Int Key)))
  setpun p = (intro (msingleton . public . first fst <$> p) . lift
    . extract) (Var . first snd <$> p)
    
  setstmt :: P.Path Key Key -> Expr a -> M Key (Free (M Key) (Rec Expr a))
  setstmt p e = intro (msingleton <$> p) (lift e)
  
  
punpath
  :: (MonadResolve m, MonadAbstract m)
  => P.VarPath
  -> m (Check (P.Path Key (Vis (Ident, Int) Key)))
punpath =
  bitraverseFree2 tag (bitraverse2 (remember2 ident) (tag))
  where
    remember2 :: (Functor f, Functor g) => (a -> f (g b)) -> a -> f (g (a, b))
    remember2 f a = ((,) a <$>) <$> f a
  

relpath
  :: (MonadResolve m, MonadAbstract m)
  => P.RelPath
  -> m (Check (P.Path Key Key))
relpath = bitraverseFree2 tag tag

  
public :: Vis Ident Key -> Key
public (Pub t) = t
public (Priv l) = (Ident l)

  
extract :: P.Path Key (Expr a) -> Expr a
extract = iter (\ (e `P.At` t) -> e `At` t)

  
rec
  :: (MonadResolve m, MonadAbstract m)
  => [P.RecStmt P.Tag P.Syntax]
  -> m (Check (Expr (Vis Int a)))
rec xs = (localIdents ls . localSymbols ss) (do
  cp' <- (fold <$>) <$> traverse2 recstmt xs
  either (return . collect) ((pure <$>) . uncurry rec') (getCollect cp'))
  where
    (ss, ls) = recctx xs
    
    rec'
      :: MonadAbstract m
      => [Free (M Key) (Rec Expr (Vis Int a))]
      -> M Key (Free (M Key) (Rec Expr (Vis Int a)))
      -> m (Expr (Vis Int a))
    rec' en se = flip Block se' . (en' ++) <$> envIdents where
      en' = mextract <$> en
      se' = mextract <$> getM se


-- | Traverse to find corresponding env and field substitutions
recstmt
  :: (MonadResolve m, MonadAbstract m)
  => P.RecStmt P.Tag P.Syntax
  -> m (Check ([Free (M Key) (Rec Expr a)], M Key (Free (M Key) (Rec Expr a))))
recstmt = go where
  go (P.DeclSym _) = return (pure mempty)
  go (P.DeclVar l) = (declvar <$>) <$> relpath (P.Ident <$> l)
  go (l `P.SetRec` e) = liftA2 (<*>) (setexpr l) (expr e)
  
  declvar
    :: P.Path Key Key
    -> ([Free (M Key) (Rec Expr a)], M Key (Free (M Key) (Rec Expr a)))
  declvar p =
    ([(Pure . abst . extract) (Var . Pub <$> p)], mempty)
    
    
abst :: Expr Var' -> Rec Expr a
abst e = toRec (e >>= \ v -> case v of
  Pub k -> return (B k)
  Priv i -> return (F (B i)))
  
  
setexpr
  :: (MonadResolve m, MonadAbstract m)
  => P.SetExpr P.Tag
  -> m (Check (Expr Var'
    -> ([Free (M Key) (Rec Expr a)], M Key (Free (M Key) (Rec Expr a)))))
setexpr = go where
  go (P.SetPath p) = (setpath <$>) <$> varpath p
  go (P.Decomp stmts) = (snd <$>) <$> usedecomp stmts
  go (P.SetDecomp l stmts) = liftA2 (liftA2 setdecomp)
    (setexpr l)
    (usedecomp stmts)
    
  setdecomp :: Semigroup m => (Expr a -> m) -> ([Key], Expr a -> m) -> Expr a -> m
  setdecomp f (ks, g) = f . rest <> g where
    rest :: Expr a -> Expr a
    rest = flip (foldl Fix) ks
    
  usedecomp
    :: (MonadResolve m, MonadAbstract m)
    => [P.Stmt P.Tag (P.SetExpr P.Tag)]
    -> m (Check ([Key], Expr Var'
      -> ([Free (M Key) (Rec Expr a)], M Key (Free (M Key) (Rec Expr a)))))
  usedecomp stmts = (fold <$>) <$> traverse2 usematchstmt stmts
  

  
varpath 
  :: (MonadResolve m, MonadAbstract m)
  => P.VarPath -> m (Check (P.Path Key Var'))
varpath = bitraverseFree2 tag (bitraverse2 ident tag)

  
setpath
  :: P.Path Key Var'
  -> Expr Var'
  -> ([Free (M Key) (Rec Expr a)], M Key (Free (M Key) (Rec Expr a)))
setpath p e = case k of
  Pub t@(Ident _) ->  ([(Pure . abst) (Var k)], msingleton t n)
  Pub t -> ([], msingleton t n)
  Priv _ -> ([n], mempty)
  where
    (k, n) = intro ((,) <$> p) (abst e)
      
        
usematchstmt
  :: (MonadResolve m, MonadAbstract m)
  => P.Stmt P.Tag (P.SetExpr P.Tag) 
  -> m (Check ([Key], Expr Var'
    -> ([Free (M Key) (Rec Expr a)], M Key (Free (M Key) (Rec Expr a)))))
usematchstmt = go where
  go (P.Pun p) = (matchpun <$>) <$> punpath p
  go (p `P.Set` l) = liftA2 (liftA2 matchset)
    (setexpr l)
    ((useextractrel <$>) <$> relpath p)
    where 
      matchset f = ((f .) <$>)
  
  matchpun
    :: P.Path Key (Vis (Ident, Int) Key)
    -> ([Key], Expr Var'
      -> ([Free (M Key) (Rec Expr a)], M Key (Free (M Key) (Rec Expr a))))
  matchpun p = (setpath (first snd <$> p) .) <$> useextractrel r where
      r = public . first fst <$> p
  
  useextractrel :: P.Path Key Key -> ([Key], Expr a -> Expr a)
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


instance Semigroup (f (An f a)) => Semigroup (An f a) where
  An x a <> b = An x (a <> b)
  a <> An x  b = An x (a <> b)
  Un fa <> Un fb = Un (fa <> fb)
    
    
instance (Semigroup (f (An f a)), Monoid (f (An f a))) => Monoid (An f a) where
  mempty = Un mempty
  
  mappend = (<>)
  
  


