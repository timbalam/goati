{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}
module Expr
  ( expr
  , stmt
  , closed
  , ScopeError(..), ScopeErrors
  )
where

import qualified Types.P as P
import Types.Expr
import Util( Collect(..), collect )

import Control.Applicative( liftA2, (<|>) )
import Control.Monad.Trans( lift )
import Data.Bitraversable
import Data.Foldable( asum )
import Data.Maybe( fromMaybe )
import Data.Semigroup
import Data.Typeable
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
  | FreeParam Label
  | OlappedMatch (P.Path P.Tag)
  | OlappedSet (P.Path P.Tag)
  | OlappedSym P.Symbol
  deriving (Eq, Show, Typeable)
  
  
type ScopeErrors = [ScopeError]
  
-- | Bindings context
data Ctx k a = Ctx { getCtx :: M.Map k a }
  deriving (Eq, Show, Functor, Foldable)

instance (Semigroup a, Ord k) => Semigroup (Ctx k a) where
  Ctx a <> Ctx b = Ctx (M.unionWith (<>) a b)
  
instance (Semigroup a, Ord k) => Monoid (Ctx k a) where
  mempty = Ctx M.empty 
  
  mappend = (<>)
  

-- | Context constructor
type Var' = Vis Ident Key
type VarPath' = P.Path Key Var'
type VarCtx a = Ctx Var' (Node a)

intropath :: P.Path Key Var' -> a -> VarCtx a
intropath p a = go (Closed a) p where
  go n (Pure x) = Ctx (M.singleton x n)
  go n (Free (p `At` x)) = go (Open (M.singleton x n) p)


-- | Resolve symbols and variables and assign unique ids
class Monad m => MonadResolve m where
  resolveSymbol :: P.Symbol -> m (Maybe Key)

  extend :: S.Set P.Symbols -> m a -> m a
  
  
resolveTag :: MonadResolve m => P.Tag -> m (Collect ScopeErrors Key)
resolveTag (P.Label l) = (return . pure) (Label l)
resolveTag (P.Symbol s) = maybe def (pure . Symbol) <$> substSymbol s where
  def = (collect . pure) (FreeSym s)
  
  
pathckrec :: [P.RecStmt P.Tag P.Syntax] -> m (Collect ScopeErrors (VarCtx a))
pathckrec = foldMap pathckrecstmt


pathckrecstmt :: MonadResolve m => P.RecStmt P.Tag P.Syntax -> m (Collect ScopeErrors (VarCtx [Expr (P.RecStmt P.Tag P.Syntax)]))
pathckrecstmt (P.DeclSym _) = pure mempty
pathckrecstmt x@(P.DeclVar l) = do 
  cl' <- bitraverse2 resolveTag (return . pure) l
  return (flip intropath [x] <$> cl')
pathckrecstmt (l `P.SetRec` r) = pathcksetexpr l >>= \ ck -> case getcollect ck of
  Left e -> return (collect e)
  Right k -> k r


pathcksetexpr
  :: MonadResolve m
  => P.SetExpr P.Tag
  -> m (Collect ScopeErrors (Expr a -> VarCtx [Expr a]))
pathcksetexpr (P.SetPath p) = do 
  cp' <- bitraverse2 resolveTag (traverse2 resolveTag) p
  return ((\ p -> intropath p . pure) <$> cp')
pathcksetexpr (P.Decomp xs) = pathckdecomp xs mempty
pathcksetexpr (P.SetDecomp l xs) = pathcksetexpr l >>= \ ck -> case getCollect ck of
  Left e -> collect e
  Rigth k -> pathckdecomp xs k


pathckdecomp
  :: MonadResolve m
  => [P.Stmt P.Tag (P.SetExpr P.Tag)]
  -> (Expr a -> VarCtx [Expr a])
  -> m (Collect ScopeError (Expr a -> VarCtx [Expr a]))
pathckdecomp xs k = foldMap pathckstmt xs >>= cn -> case getcollect cn of
    Left e -> return (collect e)
    Right x@(Open m) -> (mappend (k . fixkeys (M.keys m)) <$>) <$> buildctx x
    Right x -> buildctx x
  where
    buildctx :: Node [P.Stmt P.Tag (P.SetExpr P.Tag)] -> m (Collect ScopeErrors (Expr a -> VarCtx [Expr a])
    buildctx (Closed [x]) = buildstmt x
    buildCtx (Closed xs) = (return . collect) (OlappedMatch xs)
    buildctx (Open m) = (M.foldMapWithKey f <$>) <$> traverse2 go m where
      f t k' e = k' (e `At` t)
    
    buildstmt :: P.Stmt P.Tag (P.SetExpr P.Tag) -> m (Collect ScopeErrors (Expr a -> VarCtx [Expr a]))
    buildstmt (P.Pun p) =
      return ((\ p -> intropath p . pure) <$> bitraverse2 resolveTag (traverse2 resolveTag) p)
    buildstmt (_ `P.Set` e) = pathcksetexpr e
    
    fixkeys :: [Key] -> Expr a -> Expr a
    fixkeys = flip (foldl Fix)
  
  
pathckstmt
  :: MonadResolve m
  => P.Stmt P.Tag a
  -> m (Collect ScopeErrors (Node [P.Stmt P.Tag a]))
pathckstmt x@(P.Pun p) = do
  cl <- bitraverse2 resolveTag (resolveTag . tag) p
  return (flip intropath [x] <$> cl)
  
pathckstmt x@(p `P.Set` a) = do
  cl <- bitraverse2 resolveTag resolveTag p
  return (flip intropath [x] <$> cl)
  
  
tag :: P.Var -> P.Tag
tag (Pub t) = t
tag (Priv l) = P.Ident l
 

newtype Resolve a = Resolve (StateT Int (Reader (M.Map P.Symbol Int)) a)
  deriving (Funtor, Applicative, Monad, MonadReader (M.Map P.Symbol Int), MonadState Int)

new :: (MonadState i m, Enum i) => m i
new = state (\ i -> (succ i, i))

enumset :: (MonadState i m, Enum i) => S.Set k -> m (M.Map k i)
enumset = sequenceA . M.fromSet (const new)


instance MonadResolve Resolve where
  resolveSymbol = asks (Symbol <$> M.lookup s)

  extend s m = enumset s >>= \ s' -> local (`M.union`s') m


resolveBlock
  :: MonadResolve m
  => P.Block P.Tag P.Syntax
  -> m (Collect ScopeErrors (Expr a))
resolveBlock (P.Rec xs) = case getCollect (symbolckrec xs) of
  Left e -> return (collect e)
  Right s -> extend s ((P.Rec <$>) <$> abstractRec xs)

resolveBlock (P.Tup xs) = pure (sequenceA_ checkstmt xs) >> abstractTup xs
  

checkrec :: [P.RecStmt P.Tag P.Syntax] -> Collect ScopeErrors DeclCtx
checkrec = (if null errs then mempty else collect errs) *> ctx
  where (errs, ctx) = foldMap checkrectstmt xs

resolverecstmt :: P.RecStmt P.Tag P.Syntax -> Collect SymbolCtx SymbolCtx
resolverecstmt (P.DeclSym s) = (pure . pure) (introsym s)

checkrecstmt (P.DeclVar l) = (pure . pure . intropath) (P.Pub . P.Ident <$> l)
checkrecstmt (l `P.SetRec` _) = checksetexpr l

checkstmt :: P.Stmt P.Tag P.Syntax -> Collect DeclCtx DeclCtx
checkstmt (P.Pun l) = pure (intropath l)
checkstmt (l `P.Set` _) = (pure . intropath) (P.Pub <$> l)

checksetexpr :: P.SetExpr P.Tag -> (ScopeErrors, Collect DeclCtx DeclCtx)
checksetexpr (P.SetPath l) = (pure . pure) (intropath l)
checksetexpr (P.Decomp xs) = checkdecomp xs
checksetexpr (P.SetDecomp l xs) = checkdecomp xs <> checksetexpr l

checkdecomp
  :: [P.Stmt P.Tag (P.SetExpr P.Tag)]
  -> (ScopeErrors, Collect DeclCtx DeclCtx)
checkdecomp xs = (errs, foldmap checkmatchstmt xs) where
  errs = (either (pure . OlappedMatch . snd) mempty . getCollect) (foldMap checkstmt xs)

checkmatchstmt :: P.Stmt P.Tag (P.SetExpr P.Tag) -> Collect DeclCtx DeclCtx
checkmatchstmt (P.Pun l) = pure (intropath l)
checkmatchstmt (r `P.Set` l) = checksetexpr l


closed
  :: Ord a
  => Expr Var
  -> Either ExprErrors (Expr b)
closed = traverse (collect . pure . FreeParam)

        
-- | build executable expression syntax tree
abstract :: forall m a. MonadAbstract m => Syntax -> m (Collect ScopeErrors (Rec Expr a))
abstract = (toRec <$>) <$> go where

  go :: MonadAbstract m => Syntax -> m (Collect ScopeErrors (Expr (Var Int (Var Key a))))
  go (P.IntegerLit i) =
    (return . pure . Number) (fromInteger i)
  
  go (P.NumberLit d) =
    (return . pure) (Number d)
  
  go (P.StringLit t) =
    (return . pure) (String t)
  
  go (P.Var t) = abstract t >>= \ m -> case m of
    Left i -> B i
    Right (Just k) -> F (B k)
    Right Nothing -> (return . collect . pure) (FreeParam t)
  
  go (P.Get (e `P.At` x)) =
    liftA2 (flip At) (tag x) (go e) where
      tag (P.Pub (P.Symbol 
  
  go (P.Block b) = resolveBlock b
    
  go (P.Extend e b) =
    getCollect (liftA2 Update (coll e) (block b))
  
  go (P.Unop op e) =
    (`At` Unop op) <$> go e
    
  go (P.Binop op e w) =
    (getCollect . liftA2 updatex ((`At` Binop op) <$> coll e)) (coll w)
    where
      updatex
        :: Expr Var'
        -> Expr Var'
        -> Expr Var'
      updatex e w = (e `Update` (Block [] . M.singleton (Label "x") . Closed) (lift w)) `At` Label "return"
      
    
  coll = Collect . go


block :: P.Block Key Syntax' -> Collect ExprErrors (Expr Var')
block (Tup xs) = tupBuild <$> foldMap (Collect . stmt) xs
block (Rec xs) = recBuild <$> foldMap (Collect . recstmt) xs


-- | Symbol check
symbolckrec :: [P.RecStmt a b] -> Collect ScopeErrors (S.Set P.Symbol)
symbolckrec xs = case syms \\ nub syms of 
  [] -> pure syms
  x:xs -> collect (OlappedSym <$> x:xs)
  where
    syms = foldMap getsym xs
    
    getsym (P.DeclSym s) = pure s
    getsym _ = mempty


abstractTup :: MonadResolve m => [P.Stmt P.Tag P.Syntax] -> m (Expr Var')
abstractTup = foldMap abstractStmt xs

abstractStmt :: MonadResolve m => P.Stmt P.Tag P.Syntax -> m (M.Map Key (Node (Rec Expr Var')))
abstractStmt (P.SetPun path) =
  buildPath (Pub . public <$> path) (exprPath path))
  where
    
    exprPath (Pure a) = Var a
    exprPath (Free (p `At` x)) = Get (exprPath `At` x)
stmt (l `P.Set` r) = expr r >>= setexpr l


public (Pub t) = t
public (Priv l) = (Ident l)


fieldckrec :: MonadResolve m => [P.RecStmt P.Tag P.Syntax] -> m (Collect ScopeErrors (VarCtx P.Syntax))
fieldckrec = foldMap abstractRecStmt

recstmt :: P.RecStmt Key Syntax' -> Either ExprErrors (Build (Expr Var'))
recstmt (P.DeclSym sym) = pure mempty
recstmt (P.DeclVar path) = pure (buildVar path)
recstmt (l `P.SetRec` r) = expr r >>= setexpr l
  
  
setexpr :: P.SetExpr Key -> Expr Var' -> Either ExprErrors (Build (Expr Var'))
setexpr l r = go l where
  go (P.SetPath path) = pure (buildPath path r)
  go (P.Decomp stmts) = decomp mempty stmts
  go (P.SetDecomp l stmts) = decomp (Collect . setexpr l) stmts
  
  decomp f stmts = do 
    b <- getCollect (foldMap (pure . matchstmt) stmts)
    getCollect (matchBuild f b e)
  

matchstmt
  :: P.Stmt Key (SetExpr Key)
  -> Node (Expr a -> Collect ExprErrors (Build (Expr a)))
matchstmt (P.Pun p)   =
  nodePath (public <$> p) (Collect . setexpr (P.SetPath p))
    
matchstmt (p `P.Set` l)  =
  nodePath p (Collect . setexpr l)


