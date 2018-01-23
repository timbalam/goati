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

import Control.Applicative( liftA2 )
import Control.Monad.Trans( lift )
import Data.Bitraversable
import Data.List.NonEmpty
import Control.Monad.Free
import qualified Data.Map as M


-- | check for free parameters in expression
data ScopeError =
    ParamFree Parser.Var
  | SymbolFree Parser.Symbol
  deriving (Eq, Show)

type ScopeErrors = NonEmpty ScopeError


closed
  :: Ord a
  => Expr ListO (Key Parser.Symbol) Parser.Var
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
  
expr (Parser.Block stmts) =
  blockBuild <$> getCollect (foldMap (Collect . stmt) stmts)
    
expr (Parser.Extend e stmts) =
  (getCollect . liftA2 Update (collexpr e) . collexpr) (Parser.Block stmts)
  
expr (Parser.Unop op e) =
  (`At` Unop op) <$> expr e
  
expr (Parser.Binop op e w) =
  (getCollect . liftA2 updatex ((`At` Binop op) <$> collexpr e)) (collexpr w)
  where
    updatex
      :: Ex Parser.Symbol Parser.Var
      -> Ex Parser.Symbol Parser.Var
      -> Ex Parser.Symbol Parser.Var
    updatex e w = (e `Update` blockList [] [(Label "x", Closed (lift w))]) `At` Label "return"
    
    
collexpr = Collect . expr
      
    
stmt :: Parser.Stmt -> Either ExprErrors (Build (Ex Parser.Symbol Parser.Var))
stmt (Parser.DeclSym sym id) = pure (buildSym sym id)
stmt (Parser.SetPun path) = pure (buildPun path)
stmt (l `Parser.Set` r) = expr r >>= setexpr l
  where
    setexpr
      :: Parser.SetExpr
      -> Ex Parser.Symbol Parser.Var
      -> Either ExprErrors (Build (Ex Parser.Symbol Parser.Var))
    setexpr (Parser.SetPath path) e = pure (buildPath path e)
    
    setexpr (Parser.SetBlock stmts) e = do
      m <- getCollect (foldMap (pure . matchstmt) stmts)
      getCollect (matchBuild mempty m e)
    
    setexpr (Parser.SetDecomp se stmts) e = do
      m <- getCollect (foldMap (pure . matchstmt) stmts)
      getCollect (matchBuild (Collect . setexpr se) m e)
      
    
    matchstmt
      :: Parser.MatchStmt
      -> BuildN (Ex Parser.Symbol Parser.Var
        -> Collect ExprErrors (Build (Ex Parser.Symbol Parser.Var)))
    matchstmt (Parser.MatchPun l)   =
      buildNPath (public <$> l) (Collect . setexpr (Parser.SetPath l))
        
    matchstmt (p `Parser.Match` l)  =
      buildNPath p (Collect . setexpr l)


