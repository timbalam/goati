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
import Data.Monoid ( (<>) )
import Data.List.NonEmpty
import Control.Monad.Free
import qualified Data.Map as M


closed :: Expr a -> Either (NonEmpty (ScopeError a)) (Expr b)
closed = getCollect . traverse (Collect . Left . pure . ParamFree)
        
        
expr :: Parser.Syntax -> Either (ExprErrors Vid) (Expr Vid)
expr (Parser.IntegerLit x)            = (pure . Number)
  (fromInteger x)
expr (Parser.NumberLit x)             = pure (Number x)
expr (Parser.StringLit x)             = pure (String x)
expr (Parser.Var x)                   = (pure . Var) (coercevis x)
expr (Parser.Get (e `Parser.At` x))   = (`At` coercetag x) <$> expr e
expr (Parser.Block stmts Nothing)     = fmap Priv . blockSTree <$>
  getCollect (foldMap (Collect . stmt) stmts)
expr (Parser.Block stmts (Just e))    = liftA2 Update
  (fmap Priv . blockSTree <$> getCollect
    (foldMap (Collect . stmt) stmts))
  (expr e)
expr (e1 `Parser.Update` e2)          = liftA2 Update
  (expr e1)
  (expr e2)
expr (Parser.Unop sym e)              = error ("expr:" ++ show sym)
expr (Parser.Binop sym e1 e2)         = error ("expr: " ++ show sym)
      
    
stmt :: Parser.Stmt -> Either (ExprErrors Vid) (STree Vid)
stmt (Parser.Declare path) =
  (return . declSTree) (coercepath coercevis path)
stmt (Parser.SetPun path) =
  (return . punSTree) (coercepath coercevis path)
stmt (l `Parser.Set` r) =
  expr r >>= setexpr l where
  setexpr :: Parser.SetExpr -> Expr Vid -> Either (ExprErrors Vid) (STree Vid)
  setexpr (Parser.SetPath path) e = pure (pathSTree (coercepath coercevis path) e)
  
  setexpr (Parser.SetBlock stmts Nothing) e = do
    m <- getCollect (foldMap (pure . matchstmt) stmts)
    getCollect (matchNode mempty m e)
    
  setexpr (Parser.SetBlock stmts (Just l)) e = do
    m <- getCollect (foldMap (pure . matchstmt) stmts)
    getCollect (matchNode (Collect . setexpr (Parser.SetPath l)) m e)
      
      
  matchstmt ::
    Parser.MatchStmt -> Node (Expr Vid -> Collect (ExprErrors Vid) (STree Vid))
  matchstmt (Parser.MatchPun l)   =
    nodePath
      (coercepath (either coercetag Label . Parser.getvis) l) 
      (Collect . setexpr (Parser.SetPath l))
  matchstmt (p `Parser.Match` l)  =
    nodePath (coercepath coercetag p) (Collect . setexpr l)
    
  
  nodePath :: Path Id Tid -> a -> Node a
  nodePath path = go path . Closed
    where
      go (Pure x)                     = Open . M.singleton x
      go (Free (path `Parser.At` x))  = go path . Open . M.singleton x
      
      
  matchNode :: Monoid m => (Expr a -> m) -> Node (Expr a -> m) -> Expr a -> m
  matchNode _ (Closed f) e = f e
  matchNode k (Open m) e = k (foldr (flip Fix) e (M.keys m)) <> go (Open m) e
    where
      go :: Monoid m => Node (Expr a -> m) -> Expr a -> m
      go (Closed f) e = f e
      go (Open m) e = M.foldMapWithKey
        (\ k -> flip go (e `At` k))
        m
      
 
   
coercetag :: Tag a -> Tag b
coercetag (Label l) = Label l
  
coercevis :: Vis a -> Vis b
coercevis = either (Pub . coercetag) Priv . Parser.getvis

coercepath :: (a -> b) -> Path Parser.Syntax a -> Path Id b
coercepath co = go where
  go (Pure a) = Pure (co a)
  go (Free (b `Parser.At` x)) = Free (go b `Parser.At` coercetag x)
    

