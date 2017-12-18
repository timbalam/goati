{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Expr
  ( expr
  , stmt
  )
where

import qualified Types.Parser as Parser
import Types.Expr
import Types.Error

import Control.Applicative( liftA2 )
import Data.Foldable( foldMap )
import Control.Monad.Free
import qualified Data.Map as M
        
        
expr :: Parser.Syntax -> Either (DefnError Id (Vis Id)) (Expr (Vis Id))
expr (Parser.IntegerLit x)            = (return . Number) (fromInteger x)
expr (Parser.NumberLit x)             = return (Number x)
expr (Parser.StringLit x)             = return (String x)
expr (Parser.Var x)                   = (return . Var) (coercevis x)
expr (Parser.Get (e `Parser.At` x))   = (`At` coercetag x) <$> expr e
expr (Parser.Block stmts Nothing)     = blockSTree
  <$> getResult (foldMap (Result . stmt) stmts)
expr (Parser.Block stmts (Just e))    = liftA2 Concat
  (blockSTree <$> getResult (foldMap (Result . stmt) stmts)) (liftExpr <$> expr e)
expr (e1 `Parser.Update` e2)          = liftA2 Update (expr e1)
  (expr e2)
expr (Parser.Unop sym e)              = error ("expr:" ++ show sym)
expr (Parser.Binop sym e1 e2)         = error ("expr: " ++ show sym)
      
    
stmt :: Parser.Stmt -> Either (DefnError Id (Vis Id)) (STree (Vis Id))
stmt (Parser.Declare path) =
  (return . declSTree) (coercepath coercevis path)
stmt (Parser.SetPun path) =
  (return . punSTree) (coercepath coercevis path)
stmt (l `Parser.Set` r) =
  expr r >>= getResult . setexpr l . liftExpr where
  setexpr :: Parser.SetExpr -> Eval (Vis Id) -> Result (DefnError Id (Vis Id)) (STree (Vis Id))
  setexpr (Parser.SetPath path) e = return (pathSTree (coercepath coercevis path) e)
  
  setexpr (Parser.SetBlock stmts Nothing) e = do 
    m <- foldMap (pure . matchstmt) stmts
    blockMTree mempty m e
    
  setexpr (Parser.SetBlock stmts (Just l)) e = do
    m <- foldMap (pure . matchstmt) stmts
    (blockMTree . setexpr) (Parser.SetPath l) m e
      
      
  matchstmt ::
    Parser.MatchStmt -> MTree (Eval (Vis Id) -> Result (DefnError Id (Vis Id)) (STree (Vis Id)))
  matchstmt (Parser.MatchPun l)   =
    pathMTree
      (coercepath (either coercetag Label . Parser.getvis) l) 
      (setexpr (Parser.SetPath l))
  matchstmt (p `Parser.Match` l)  =
    pathMTree (coercepath coercetag p) (setexpr l)
 
   
coercetag :: Tag a -> Tag b
coercetag (Label l) = Label l
  
coercevis :: Vis a -> Vis b
coercevis = either (Pub . coercetag) Priv . Parser.getvis

coercepath :: (a -> b) -> Path Parser.Syntax a -> Path Id b
coercepath co = go where
  go (Pure a) = Pure (co a)
  go (Free (b `Parser.At` x)) = Free (go b `Parser.At` coercetag x)
    

