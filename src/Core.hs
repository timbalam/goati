{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings, RecordWildCards #-}

module Core
  ( expr )
where

import Types.Parser as P hiding ( Tag )
import Types.Core
import qualified Types.Error as E

import Control.Applicative (liftA2)
import Data.Foldable (foldMap)
import Control.Monad.Free
import qualified Data.Map as M
        
        
expr :: P.Expr (Vis Tag) -> Maybe (Expr (Vis Tag))
expr (P.IntegerLit x) =
  (return . Number) (fromInteger x)
  
expr (P.NumberLit x) =
  return (Number x)

expr (P.StringLit x) =
  return (String x)
  
expr (P.Var x) =
  return (Var x)
  
expr (P.Get (expr `P.At` x)) =
  (`At` x) <$> expr expr
    
expr (P.Block (P.BlockExpr stmts)) =
  do
    s <- foldMap stmt stmts
    return (blockS s es)
  
expr (x `P.Update` P.BlockExpr stmts exprs) =
  (liftA2 Update (expr x) . expr . P.Block) (P.BlockExpr stmts exprs)

expr (P.Unop sym x) =
  Nothing

expr (P.Binop sym x y) =
  Nothing
      
    
stmt :: P.Stmt Tag -> Maybe (S (Vis Tag))
stmt (P.Declare path) =
  (return . pathS path) (varPath path)
  where 
    varPath :: P.Path (Vis Tag) -> Expr (Vis Tag)
    varPath (Pure x) = Var x
    varPath (Free (path `P.At` x)) = varPath path `V.At` x

stmt (P.SetPun path) =
  return (punS path)

stmt (P.SetPath path `P.Set` r) =
  do
    e <- expr r
    return (pathS path e)
    
stmt (P.SetBlock stmts ml `P.Set` r) =
  do
    e <- expr r
    m <- foldMap matchStmt stmts
    blockM (maybe (const mempty) pathS ml) m e
    
  where
    matchStmt :: P.MatchStmt (P.Path (Vis Tag)) (P.Path Tag) -> M (Expr (Vis Tag) -> Maybe (S (Vis Tag)))
    matchStmt (P.MatchPun l) =
      pathM (vis id id <$> l) (return . pathS l)

    matchStmt (p `P.Match` l) =
      pathM p (setExpr l)
      
   
    

