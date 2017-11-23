module Core
  ( expr )
where

import qualified Types.Parser as TP
import Types.Core
import qualified Types.Error as E

import Control.Applicative (liftA2)
import Data.Foldable (foldMap)
import Control.Monad.Free
import qualified Data.Map as M
        
        
expr :: TP.Expr (Vis Tag) -> MRes (Expr (Vis Tag))
expr (TP.IntegerLit x) =
  (return . Number) (fromInteger x)
  
expr (TP.NumberLit x) =
  return (Number x)

expr (TP.StringLit x) =
  return (String x)
  
expr (TP.Var x) =
  return (Var x)
  
expr (TP.Get (e `TP.At` x)) =
  (`At` x) <$> expr e
    
expr (TP.Block stmts) =
  do
    s <- foldMap stmt stmts
    return (blockS s)
  
expr (e1 `TP.Update` e2) =
  liftA2 Update (expr e1) (expr e2)

expr (TP.Unop sym e) =
  MRes Nothing

expr (TP.Binop sym e1 e2) =
  MRes Nothing
      
    
stmt :: TP.Stmt (Vis Tag) -> MRes (S (Vis Tag))
stmt (TP.Declare path) =
  (return . pathS path) (varPath path)
  where 
    varPath :: TP.Path (Vis Tag) -> Expr (Vis Tag)
    varPath (Pure x) = Var x
    varPath (Free (path `TP.At` x)) = varPath path `At` x

stmt (TP.SetPun path) =
  return (punS path)
  
stmt (l `TP.Set` r) =
  do
    e <- expr r
    setexpr l e
    
  where
    setexpr :: TP.SetExpr (Vis Tag) -> Expr (Vis Tag) -> MRes (S (Vis Tag))
    setexpr (TP.SetPath path) e =
      return (pathS path e)
      
    setexpr (TP.SetBlock stmts) e =
      do 
        m <- foldMap (pure . matchstmt) stmts
        blockM mempty m e

    setexpr (TP.SetConcat stmts l) e =
      do
        m <- foldMap (pure . matchstmt) stmts
        (blockM . setexpr) (TP.SetPath l) m e
      
      
    matchstmt :: TP.MatchStmt (Vis Tag) -> M (Expr (Vis Tag) -> MRes (S (Vis Tag)))
    matchstmt (TP.MatchPun l) =
      pathM (vis id id <$> l) (return . pathS l)

    matchstmt (p `TP.Match` l) =
      pathM p (setexpr l)
      
   
    

