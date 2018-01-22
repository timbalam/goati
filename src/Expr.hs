{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}
module Expr
  ( expr
  , stmt
  , closed
  )
where

import qualified Types.Parser as Parser
import Types.Expr
import Types.Error
import Util( Collect(..) )

import Control.Applicative( liftA2 )
import Control.Monad.Trans( lift )
--import Data.Foldable( foldMap )
--import Data.Monoid ( (<>) )
import Data.List.NonEmpty
import Control.Monad.Free
import qualified Data.Map as M
      

data ScopeErrors = ScopeErrors (NonEmpty Label)

closed :: Expr k a -> Either ScopeErrors) (Expr k b)
closed = getCollect . traverse (Collect . Left . pure . ParamFree)

        
expr :: Parser.Syntax -> Either ExprErrors (Ex Parser.Symbol)
expr (Parser.IntegerLit i) =
  (pure . Number) (fromInteger i)
  
expr (Parser.NumberLit d) =
  pure (Number d)
  
expr (Parser.StringLit s) =
  pure (String s)
  
expr (Parser.Var a) =
  (pure . Var) (var a)
  
expr (Parser.Get (e `Parser.At` x)) =
  (`At` tag x) <$> expr e
  
expr (Parser.Block stmts) =
  blockSTree <$> getCollect (foldMap (Collect . stmt) stmts)
    
expr (Parser.Extend e stmts) =
  (liftA2 Update (expr e) . expr) (Parser.Block stmts)
  
expr (Parser.Unop op e) =
  (`At` Unop op) <$> expr e where
  
expr (Parser.Binop op e w) =
  liftA2 applyop ((`At` Binop op) <$> expr e) (expr w)
  where
    applyop :: Ex Parser.Symbol -> Ex Parser.Symbol -> Ex Parser.Symbol
    applyop e w = (e `Update` blockList [] [(Label "x", Pure (lift w))]) `At` Label "return"
      
    
      
    
stmt :: Parser.Stmt -> Either ExprErrors (Build (Ex Parser.Symbol))
stmt (Parser.DeclSym sym) =
  pure mempty
  
stmt (Parser.SetPun path) =
  punSTree path
  
stmt (l `Parser.Set` r) =
  expr r >>= setexpr l
  where
    setexpr
      :: Parser.SetExpr
      -> Ex Parser.Symbol
      -> Either ExprErrors (Build (Ex Parser.Symbol))
    setexpr (Parser.SetPath path) e = pure (buildPath path e)
    
    setexpr (Parser.SetBlock stmts) e = do
      m <- getCollect (foldMap (pure . matchstmt) stmts)
      getCollect (matchNode mempty m e)
    
    setexpr (Parser.SetDecomp se stmts) e = do
      m <- getCollect (foldMap (pure . matchstmt) stmts)
      getCollect (matchNode (Collect . setexpr se) m e)
      
    
    matchstmt
      :: Parser.MatchStmt
      -> Node (Ex Parser.Symbol -> Collect ExprErrors (Build (Ex Parser.Symbol)))
    matchstmt (Parser.MatchPun l)   =
      buildNPath (public <$> l) (Collect . setexpr (Parser.SetPath l))
        
    matchstmt (p `Parser.Match` l)  =
      buildNPath p (Collect . setexpr l)


