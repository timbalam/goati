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
import Data.Typeable
import Data.List.NonEmpty( NonEmpty )
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M


-- | check for free parameters in expression
data ExprError =
    FreeSym Parser.Symbol
  | FreeParam Parser.Var
  | OlappedMatch Paths
  | OlappedSet Parser.Var Paths
  | OlappedSym Parser.Symbol
  deriving (Eq, Show, Typeable)

type ExprErrors = NonEmpty ExprError
type Var' = Vis Ident Key
type Syntax' = Parser.Expr Key Var'


newtype Symbols = S_ { getSymbols :: S.Set Parser.Symbol }

singleton :: Parser.Symbol -> Symbols
singleton = S_ . S.singleton

mergeSymbols :: Symbols -> Symbols -> Collect ExprErrors Symbols
mergeSymbols (S_ a) (S_ b) = S_ <$> m where
  m = case S.toList (S.intersection a b) of
    [] -> pure (S.union a b)
    x:xs -> collect (OlappedSym <$> x:|xs)
    
instance Monoid (Collect ExprErrors Symbols) where
  mempty = pure (S.empty)
  
  a `mappend` b = (either collect id . getCollect) (liftA2 mergeSymbols a b)


type SymbolMap = M.Map Parser.Symbol Int
type Resolve a = StateT Int (Reader SymbolMap) (Collect ExprErrors a)


next :: (MonadState i m, Enum i) => m i
next = state (\ i -> (succ i, i))


-- | Resolve symbols and assign ids
symbolise :: Parser.Syntax -> Resolve Parser.Syntax'
symbolise = go where
  go (Block b) = (Block <$>) <$> symboliseBlock b
  go (e `Extend` b) = liftA2 (liftA2 Extend) (go e) (symboliseBlock b)
  go e = sequenceA (bitraverse symboliseTag symboliseVar e)
  
  symboliseBlock :: Parser.Block Parser.Tag Parser.Syntax -> Resolve (Parser.Block Key Syntax')
  symboliseBlock (Rec xs) = case getCollect cOfs of
    Left e -> pure (collect e)
    Right s -> do 
      m <- enumsymbols s
      local (`M.union` m) ((Rec <$>) <$> symboliseStmts xs)
    where
      cOfs = getSymbols <$> foldMap getsymbol xs
  symboliseBlock (Tup xs) = (Tup <$>) <$> symboliseStmts xs
  
  getsymbol :: Parser.RecStmt a b -> Collect ExprErrors Symbols
  getsymbol (DeclSym s) = singleton s
  getsymbol _ = mempty
  
  enumsymbols :: (MonadState i m, Enum i) => S.Set k -> m (M.Map k i)
  enumsymbols = sequenceA . M.fromSet (\ _ -> next)
  
  symboliseStmts :: Bitraversable t => [t Parser.Tag Parser.Syntax] -> Resolve (t Key Syntax')
  symboliseStmts xs = sequenceA <$> traverse symboliseStmt xs
      
  symboliseStmt
    :: Bitraversable t
    => t Parser.Tag Parser.Syntax
    -> Resolve (t Key Syntax')
  symboliseRecStmt = bisequenceA <$> bitraverse symboliseTag symbolise
  
  symboliseTag :: Parser.Tag -> Resolve Key
  symboliseTag (Parser.Ident l) = (return . pure) (Ident l)
  symboliseTag (Parser.Symbol s) = asks (maybe def (pure . Symbol) . M.lookup s)
    where
      def = (collect . pure) (FreeSym s)
  
  symboliseVar :: Parser.Var -> Resolve Var'
  symboliseVar = sequenceA . traverse symboliseTag


closed
  :: Ord a
  => Expr Var'
  -> Either ScopeErrors (Expr b)
closed e = hoistExpr (M.fromList . getListO) <$> getCollect
  (bitraverse
    (traverse (collect . pure . SymbolFree))
    (collect . pure . ParamFree)
    e)

        
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


