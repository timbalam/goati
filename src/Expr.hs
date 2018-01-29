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
data ScopeError =
    ParamFree Parser.Var
  | SymbolFree Parser.Symbol
  deriving (Eq, Show, Typeable)

type ScopeErrors = NonEmpty ScopeError


closed
  :: Ord a
  => Ex Parser.Symbol Parser.Var
  -> Either ScopeErrors (Expr M.Map (Key a) b)
closed e = hoistExpr (M.fromList . getListO) <$> getCollect
  (bitraverse
    (traverse (collect . pure . SymbolFree))
    (collect . pure . ParamFree)
    e)
      
      
-- | Alias
type Ex a b = Expr ListO (Key a) b
        
-- | build executable expression syntax tree
expr :: Parser.Syntax -> Either ExprErrors (Ex Parser.Symbol Parser.Var)
expr (Parser.IntegerLit i) =
  (pure . Number) (fromInteger i)
  
expr (Parser.NumberLit d) =
  pure (Number d)
  
expr (Parser.StringLit t) =
  pure (String t)
  
expr (Parser.Var a) =
  pure (Var a)
  
expr (Parser.Get (e `Parser.At` x)) =
  (`At` tag x) <$> expr e
  
expr (Parser.Block b) =
  getCollect (block b)
    
expr (Parser.Extend e b) =
  getCollect (liftA2 Update (collexpr e) (block b))
  
expr (Parser.Unop op e) =
  (`At` Unop op) <$> expr e
  
expr (Parser.Binop op e w) =
  (getCollect . liftA2 updatex ((`At` Binop op) <$> collexpr e)) (collexpr w)
  where
    updatex
      :: Ex Parser.Symbol Parser.Var
      -> Ex Parser.Symbol Parser.Var
      -> Ex Parser.Symbol Parser.Var
    updatex e w = (e `Update` (Block [] . ListO) [(Label "x", Closed (lift w))]) `At` Label "return"
    
    
collexpr = Collect . expr


block :: Parser.Block -> Collect ExprErrors (Build (Ex Parser.Symbol Parser.Var))
block (Parser.B_ stmts m recstmts) = maybe b (liftA2 Update b . collexpr) m
  where
    b = blockBuild <$> (foldMap (Collect . stmt) stmts <> foldMap (Collect . recstmts) recstmts)


stmt :: Parser.Stmt -> Either ExprErrors (Build (Ex Parser.Symbol Parser.Var))
stmt (Parser.SetPun path) = pure (buildPun path)
stmt (l `Parser.Set` r) = expr r >>= setexpr l . R Lifted

    
recstmt :: Parser.RecStmt -> Either ExprErrors (Build (Ex Parser.Symbol Parser.Var))
recstmt (Parser.DeclSym sym) = pure (buildSym sym)
recstmt (Parser.DeclVar path) = pure (buildVar path)
recstmt (l `Parser.SetRec` r) = expr r >>= setexpr l . R Current
  
  
setexpr
  :: Parser.SetExpr
  -> Ref (Ex Parser.Symbol Parser.Var)
  -> Either ExprErrors (Build (Ex Parser.Symbol Parser.Var))
setexpr (Parser.SetPath path) e = pure (buildPath path e)

setexpr (Parser.SetBlock stmts m) e = do
  b <- getCollect (foldMap (pure . matchstmt) stmts)
  getCollect (matchBuild f b e)
  where
    f = maybe mempty (\ se -> Collect . setexpr se) m
  

matchstmt
  :: Parser.MatchStmt
  -> BuildN (Ref (Ex Parser.Symbol Parser.Var)
    -> Collect ExprErrors (Build (Ex Parser.Symbol Parser.Var)))
matchstmt (Parser.MatchPun p)   =
  buildNPath (public <$> p) (Collect . setexpr (Parser.SetPath p))
    
matchstmt (p `Parser.Match` l)  =
  buildNPath p (Collect . setexpr l)


