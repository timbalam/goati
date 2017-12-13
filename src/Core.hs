{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Core
  ( expr
  , stmt
  )
where

import qualified Types.Parser as Parser
import Types.Core
--import qualified Types.Error as E

import Control.Applicative( liftA2 )
import Data.Foldable( foldMap )
import Control.Monad.Free
import qualified Data.Map as M
        
        
expr :: Parser.Syntax -> MRes (Expr (Vis Id))
expr (Parser.IntegerLit x)            = (return . Number) (fromInteger x)
expr (Parser.NumberLit x)             = return (Number x)
expr (Parser.StringLit x)             = return (String x)
expr (Parser.Var x)                   = (return . Var) (coercevis x)
expr (Parser.Get (e `Parser.At` x))   = (`At` coercetag x) <$> expr e
expr (Parser.Block stmts Nothing)     = blockS <$> foldMap stmt stmts
expr (Parser.Block stmts (Just e))    = liftA2 Concat (blockS <$> foldMap stmt stmts) (expr e)
expr (e1 `Parser.Update` e2)          = liftA2 Update (expr e1) (expr e2)
expr (Parser.Unop sym e)              = MRes Nothing
expr (Parser.Binop sym e1 e2)         = MRes Nothing
      
    
stmt :: Parser.Stmt -> MRes (S (Vis Id))
stmt (Parser.Declare path) = (return . declS) (coercepath coercevis path)
stmt (Parser.SetPun path) = (return . punS) (coercepath coercevis path)
stmt (l `Parser.Set` r) = expr r >>= setexpr l where
  setexpr :: Parser.SetExpr -> Expr (Vis Id) -> MRes (S (Vis Id))
  setexpr (Parser.SetPath path) e = return (pathS (coercepath coercevis path) e)
  
  setexpr (Parser.SetBlock stmts Nothing) e = do 
    m <- foldMap (pure . matchstmt) stmts
    blockM mempty m e
    
  setexpr (Parser.SetBlock stmts (Just l)) e = do
    m <- foldMap (pure . matchstmt) stmts
    (blockM . setexpr) (Parser.SetPath l) m e
      
      
  matchstmt ::
    Parser.MatchStmt -> M (Expr (Vis Id) -> MRes (S (Vis Id)))
  matchstmt (Parser.MatchPun l)   = (pathM (coercepath (either coercetag Label . Parser.getvis) l) . setexpr) (Parser.SetPath l)
  matchstmt (p `Parser.Match` l)  = pathM (coercepath coercetag p) (setexpr l)
 
   
coercetag :: Tag a -> Tag b
coercetag (Label l) = Label l
  
coercevis :: Vis a -> Vis b
coercevis = either (Pub . coercetag) Priv . Parser.getvis

coercepath :: (a -> b) -> Path Parser.Syntax a -> Path Id b
coercepath co = go where
  go (Pure a) = Pure (co a)
  go (Free (b `Parser.At` x)) = Free (go b `Parser.At` coercetag x)
    

