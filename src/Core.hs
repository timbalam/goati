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
        
        
expr :: Parser.Expr (Vis Tag) -> MRes (Expr (Vis Tag))
expr (Parser.IntegerLit x)            = (return . Number) (fromInteger x)
expr (Parser.NumberLit x)             = return (Number x)
expr (Parser.StringLit x)             = return (String x)
expr (Parser.Var x)                   = return (Var x)  
expr (Parser.Get (e `Parser.At` x))   = (`At` x) <$> expr e
expr (Parser.Block stmts Nothing)     = blockS <$> foldMap stmt stmts
expr (Parser.Block stmts (Just e))    = liftA2 Concat (blockS <$> foldMap stmt stmts) (expr e)
expr (e1 `Parser.Update` e2)          = liftA2 Update (expr e1) (expr e2)
expr (Parser.Unop sym e)              = MRes Nothing
expr (Parser.Binop sym e1 e2)         = MRes Nothing
      
    
stmt :: Parser.Stmt (Vis Tag) -> MRes (S (Vis Tag))
stmt (Parser.Declare path) = (return . pathS path) (undefPath path)
  where 
    undefPath :: Parser.Path (Vis Tag) -> Expr (Vis Tag)
    undefPath (Pure _) = Undef
    undefPath (Free (path `Parser.At` x)) = undefPath path `At` x

stmt (Parser.SetPun path) = return (punS path)
  
stmt (l `Parser.Set` r) = expr r >>= setexpr l
  where
    setexpr :: Parser.SetExpr (Vis Tag) -> Expr (Vis Tag) -> MRes (S (Vis Tag))
    setexpr (Parser.SetPath path) e = return (pathS path e)
      
    setexpr (Parser.SetBlock stmts Nothing) e =
      do 
        m <- foldMap (pure . matchstmt) stmts
        blockM mempty m e

    setexpr (Parser.SetBlock stmts (Just l)) e =
      do
        m <- foldMap (pure . matchstmt) stmts
        (blockM . setexpr) (Parser.SetPath l) m e
      
      
    matchstmt ::
      Parser.MatchStmt (Vis Tag) -> M (Expr (Vis Tag) -> MRes (S (Vis Tag)))
    matchstmt (Parser.MatchPun l)   = pathM (Parser.vis id id <$> l) (return . pathS l)
    matchstmt (p `Parser.Match` l)  = pathM p (setexpr l)
      
   
    

