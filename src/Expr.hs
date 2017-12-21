{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Expr
  ( expr
  , stmt
  , closed
  )
where

import qualified Types.Parser as Parser
import Types.Expr
import Types.Error

import Control.Applicative( liftA2 )
import Data.Foldable( foldMap )
import Data.List.NonEmpty
import Control.Monad.Free
import qualified Data.Map as M


closed :: Eval a -> Either (NonEmpty a) (Eval b)
closed = getCollect . traverse (Collect . Left . pure)
        
        
expr :: Parser.Syntax -> Either (Errors (Vis Id)) (Expr (Vis Id))
expr (Parser.IntegerLit x)            = (pure . Val . Number)
  (fromInteger x)
expr (Parser.NumberLit x)             = (pure . Val) (Number x)
expr (Parser.StringLit x)             = (pure . Val) (String x)
expr (Parser.Var x)                   = (pure . Var) (coercevis x)
expr (Parser.Get (e `Parser.At` x))   = Val . (`At` coercetag x)
  . liftExpr <$> expr e
expr (Parser.Block stmts Nothing)     = blockSTree <$>
  getCollect (foldMap (Collect . stmt) stmts)
expr (Parser.Block stmts (Just e))    = Val <$> (liftA2 Concat
  (liftExpr . blockSTree <$> getCollect
    (foldMap (Collect . stmt) stmts))
  (expr e))
expr (e1 `Parser.Update` e2)          = Val <$>
  liftA2 Update (liftExpr <$> expr e1) (liftExpr <$> expr e2)
expr (Parser.Unop sym e)              = error ("expr:" ++ show sym)
expr (Parser.Binop sym e1 e2)         = error ("expr: " ++ show sym)
      
    
stmt :: Parser.Stmt -> Either (Errors (Vis Id)) (STree (Vis Id))
stmt (Parser.Declare path) =
  (return . declSTree) (coercepath coercevis path)
stmt (Parser.SetPun path) =
  (return . punSTree) (coercepath coercevis path)
stmt (l `Parser.Set` r) =
  expr r >>= setexpr l where
  setexpr :: Parser.SetExpr -> Expr (Vis Id) -> Either (Errors (Vis Id)) (STree (Vis Id))
  setexpr (Parser.SetPath path) e = pure (pathSTree (coercepath coercevis path) e)
  
  setexpr (Parser.SetBlock stmts Nothing) e = do
    m <- getCollect (foldMap (pure . matchstmt) stmts)
    getCollect (blockMTree mempty m e)
    
  setexpr (Parser.SetBlock stmts (Just l)) e = do
    m <- getCollect (foldMap (pure . matchstmt) stmts)
    getCollect (blockMTree (Collect . setexpr (Parser.SetPath l)) m e)
      
      
  matchstmt ::
    Parser.MatchStmt -> MTree (Expr (Vis Id) -> Collect (Errors (Vis Id)) (STree (Vis Id)))
  matchstmt (Parser.MatchPun l)   =
    pathMTree
      (coercepath (either coercetag Label . Parser.getvis) l) 
      (Collect . setexpr (Parser.SetPath l))
  matchstmt (p `Parser.Match` l)  =
    pathMTree (coercepath coercetag p) (Collect . setexpr l)
 
   
coercetag :: Tag a -> Tag b
coercetag (Label l) = Label l
  
coercevis :: Vis a -> Vis b
coercevis = either (Pub . coercetag) Priv . Parser.getvis

coercepath :: (a -> b) -> Path Parser.Syntax a -> Path Id b
coercepath co = go where
  go (Pure a) = Pure (co a)
  go (Free (b `Parser.At` x)) = Free (go b `Parser.At` coercetag x)
    

