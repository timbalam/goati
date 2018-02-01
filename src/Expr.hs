{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}
module Expr
  ( expr
  , stmt
  , closed
  , ScopeError(..), ScopeErrors
  )
where

import qualified Types.Parser as Parser
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
    FreeSym Parser.Symbol
  | FreeParam Label
  | OlappedMatch (Paths Void)
  | OlappedSet Parser.Tag (Paths Void)
  | OlappedSym Parser.Symbol
  deriving (Eq, Show, Typeable)
  

type ScopeErrors = NonEmpty ScopeError


data Paths a =
    Tip a 
  | Branch (M.Map Parser.Tag (Paths a))
  deriving (Eq, Show)
  
  
instance Semigroup (Paths Void) where
  Branch a <> Branch b = Branch (M.unionWith (<>) a b)
  
  
listPaths :: Paths a -> [Parser.Path Parser.Tag Parser.Tag]
listPaths (Tip _) = []
listPaths (Branch m) = M.foldMapWithKey (go . Pure) m where
  go :: Parser.Path Parser.Tag a -> Paths -> [Parser.Path Parser.Tag a]
  go _ (Tip _) = []
  go p (Branch m) = if M.null m then [p] else 
    M.foldMapWithKey (go . Free . Parser.At p) m

    
emptyPath = Branch M.empty


disjointPaths :: Paths a -> Paths a -> Collect (Paths Void) (Paths a)
disjointPaths (Tip _) a = collect emptyBranch
disjointPaths a (Tip _) = collect emptyBranch
disjointPaths (Branch a) (Branch b) = Branch <$> unionWith f a b where
  f k a b = first (Branch . M.singleton k) (disjointPaths a b)


-- | Binding context
newtype Ctx k s a = Ctx 
  { symbols :: M.Map Parser.Symbol s
  , bindings :: M.Map k a
  }
  
  
emptyCtx :: Ctx k s a
emptyCtx = Ctx S.empty M.empty


-- | Context of block declarations
type DeclCtx = Ctx Parser.Tag () (Paths ())

disjointCtx :: DeclCtx -> DeclCtx -> Collect ScopeErrors DeclCtx
disjointCtx (Ctx symbolsa bindingsa) (Ctx symbolsb bindingsb) = Ctx
  <$> disjointSymbols symbolsa symbolsb
  <*> disjointBindings bindingsa bindingsb
  where
    disjointSymbols a b = unionWith f where
      f k _ _ = (collect . pure) (OlappedSym k)
      
    disjointBindings = unionWith f where
      f k a b = first (pure . OlappedSet k) (disjointPaths a b)
      
      
instance Monoid (Collect ScopeErrors DeclCtx) where
  mempty = pure emptyCtx
  
  a `mappend` b = (join . liftA2) (disjointCtx a b)
      
  
-- | Context of block variable bindings
type VarCtx = Ctx Label Int Int
      
      
extendCtx :: VarCtx -> VarCtx -> VarCtx
extendCtx (Ctx symbolsa bindingsa) (Ctx symbolsb bindingsb) =
  Ctx
    (M.union symbolsb symbolsa)
    (M.union bindingsb (M.map (+sz) bindingsa))
  where
    sz = M.size bindingsb
      
      
-- | Context constructors
introsym :: Parser.Symbol -> DeclCtx
introsym s = emptyCtx { symbols = M.singleton s () }

intropath :: Parser.Path Parser.Tag Parser.Var -> DeclCtx
intropath = go (Tip ()) where
  go ps (Pure v) = emptyCtx { bindings = M.singleton (tag v) ps }
  go ps (Free (p `At` x)) = (go . Branch) (M.singleton x ps) p
  
  tag (Parser.Pub t) = t
  tag (Parser.Priv l) = Parser.Label l
      

-- | Resolve symbols and variables and assign unique ids
type Resolve = StateT Int (Reader (Ctx Label Int ()))
type Syntax' = Parser.Expr Key (Either Key Int)

next :: (MonadState i m, Enum i) => m i
next = state (\ i -> (succ i, i))

close :: Parser.Syntax -> Resolve (Parser.Expr Key (Either Key Int))
close = resolveExpr

resolveExpr
  :: Parser.Expr Parser.Tag Parser.Var -> Resolve (ScopeErrors, Syntax')
resolveExpr = go where
  go (Parser.Block b) = (Parser.Block <$>) <$> resolveBlock b
  go (e `Parser.Extend` b) = liftA2 (liftA2 Parser.Extend) (go e) (resolveBlock b)
  go e = pure <$> bitraverse resolveTag resolveVar e
  
  resolveBlock :: Parser.Block Parser.Tag Parser.Syntax -> Resolve (ScopeErrors, Parser.Block Key Syntax')
  resolveBlock (Parser.Rec xs) = do 
    symbols' <- enumsymbols (symbols ctx)
    let bindings' = filterlabels (bindings ctx)
    local (`extendCtx` ctx { symbols =  symbols', bindings = bindings' }) (((,) e . Parser.Rec <$>) <$> resolveStmts xs)
    where
      (e, ctx) = foldMap checkrecstmt xs
  resolveBlock (Parser.Tup xs) = sequenceA_ checkstmt xs *> (Parser.Tup <$>) <$> resolveStmts xs
  
  resolveStmts :: Bitraversable t => [t Parser.Tag Parser.Syntax] -> Resolve (t Key Syntax')
  resolveStmts xs = sequenceA <$> traverse resolveStmt xs
      
  resolveStmt
    :: Bitraversable t => t Parser.Tag Parser.Syntax -> Resolve (t Key Syntax')
  resolveStmt = bisequenceA <$> bitraverse resolveTag resolveExpr
  
  resolveTag :: MonadState EnvCtx m => Parser.Tag -> m (Collect ScopError Key)
  resolveTag (Parser.Ident l) = (return . pure) (Ident l)
  resolveTag (Parser.Symbol s) = asks (maybe def (pure . Symbol) . M.lookup s . symbols) where
      def = (collect . pure) (FreeSymbol s)
  
  resolveVar :: MonadState EnvCtx m => Parser.Var -> m (Collect ScopeError (Either Key Int))
  resolveVar (Parser.Pub t) = (Left <$>) <$> resolveTag
  resolveVar (Parser.Priv l) = asks (maybe def (pure . Right) . M.lookup l . bindings) where
    def = (collect . pure) (FreeParam l)
  
  checkrecstmt :: Parser.RecStmt a b -> (ScopeErrors, Ctx ())
  checkrecstmt (Parser.DeclSym s) = pure (introsym s)
  checkrecstmt (Parser.DeclVar l) = pure (intropath (Parser.Pub . Parser.Ident <$> l) ())
  checkrecstmt (l `Parser.SetRec` r) = checksetexpr l
  
  
  filterlabels :: M.Map Parser.Var a -> M.Map Label a
  filterlabels = M.fromAscList . mapMaybe getlabel . M.toAscList

  label :: Parser.Var -> Maybe Label
  label (Parser.Priv l ) = Just l
  label (Parser.Pub (Parser.Label l)) = Just l
  label (Parser.Pub (Parser.Symbol _)) = Nothing
  
  enumsymbols :: (MonadState i m, Enum i) => M.Map k a -> m (M.Map k i)
  enumsymbols = traverse (const next)


closed
  :: Ord a
  => Expr Var
  -> Either ExprErrors (Expr b)
closed = traverse (collect . pure . FreeParam)

        
-- | build executable expression syntax tree
expr :: Syntax' -> Either ExprErrors (Expr Var')
expr = go where
  go (Parser.IntegerLit i) =
    (pure . Number) (fromInteger i)
  
  go (Parser.NumberLit d) =
    pure (Number d)
  
  go (Parser.StringLit t) =
    pure (String t)
  
  go (Parser.Var t) = pure (Var t)
  
  go (Parser.Get (e `Parser.At` x)) =
    (`At` x) <$> go e
  
  go (Parser.Block b) =
    getCollect (block b)
    
  go (Parser.Extend e b) =
    getCollect (liftA2 Update (coll e) (block b))
  
  go (Parser.Unop op e) =
    (`At` Unop op) <$> go e
    
  go (Parser.Binop op e w) =
    (getCollect . liftA2 updatex ((`At` Binop op) <$> coll e)) (coll w)
    where
      updatex
        :: Expr Var'
        -> Expr Var'
        -> Expr Var'
      updatex e w = (e `Update` (Block [] . M.singleton (Label "x") . Closed) (lift w)) `At` Label "return"
      
    
  coll = Collect . go


block :: Parser.Block Key Syntax' -> Collect ExprErrors (Expr Var')
block (Tup xs) = tupBuild <$> foldMap (Collect . stmt) xs
block (Rec xs) = recBuild <$> foldMap (Collect . recstmt) xs


stmt :: Parser.Stmt Key Syntax' -> Either ExprErrors (Build (Expr Var'))
stmt (Parser.SetPun path) = pure (buildPath (Pub . public <$> path) (exprPath path))
  where
    
    exprPath (Pure a) = Var a
    exprPath (Free (p `At` x)) = Get (exprPath `At` x)
stmt (l `Parser.Set` r) = expr r >>= setexpr l


public (Pub t) = t
public (Priv l) = (Ident l)

    
recstmt :: Parser.RecStmt Key Syntax' -> Either ExprErrors (Build (Expr Var'))
recstmt (Parser.DeclSym sym) = pure mempty
recstmt (Parser.DeclVar path) = pure (buildVar path)
recstmt (l `Parser.SetRec` r) = expr r >>= setexpr l
  
  
setexpr :: Parser.SetExpr Key -> Expr Var' -> Either ExprErrors (Build (Expr Var'))
setexpr l r = go l where
  go (Parser.SetPath path) = pure (buildPath path r)
  go (Parser.Decomp stmts) = decomp mempty stmts
  go (Parser.SetDecomp l stmts) = decomp (Collect . setexpr l) stmts
  
  decomp f stmts = do 
    b <- getCollect (foldMap (pure . matchstmt) stmts)
    getCollect (matchBuild f b e)
  

matchstmt
  :: Parser.Stmt Key (SetExpr Key)
  -> Node (Expr a -> Collect ExprErrors (Build (Expr a)))
matchstmt (Parser.Pun p)   =
  nodePath (public <$> p) (Collect . setexpr (Parser.SetPath p))
    
matchstmt (p `Parser.Set` l)  =
  nodePath p (Collect . setexpr l)


