{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}
module Expr
  ( expr
  , stmt
  , closed
  , symexpr
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


-- | traverse syntax tree and assign unique symbol ids
symbolIds :: Parser.Syntax () -> StateT Int (Reader IdS) (Parser.Syntax Id)
symbolIds (Parser.IntegerLit i) = pure (Parser.IntegerLit i)
symbolIds (Parser.NumberLit d) = pure (Parser.NumberLit d)
symbolIds (Parser.StringLit s) = pure (Parser.StringLit s)
symbolIds (Parser.Var a) = pure (Parser.Var a)
symbolIds (Parser.Get (e `Parser.At` x)) = Parser.Get . (`Parser.At` x) <$> anon (symbolIds e)
symbolIds (Parser.Block stmts) = Parser.Block <$> traverse symbolIdsStmt stmts
symbolIds (Parser.Extend e stmts) =
  liftA2 Parser.Extend (anon (symbolIds e)) (anon (traverse symbolIdsStmt stmts))
symbolIds (Parser.Unop op e) =
  Parser.Unop op <$> anon (symbolIds e)
symbolIds (Parser.Binop op e w) =
  liftA2 (Parser.Binop op)
    (anon (symbolIds e))
    (anon (symbolIds w))
    
    
symbolise :: Parser.Syntax () -> IdS -> Parser.Syntax Id
symbolise m = runReader (evalStateT (symbolIds m) 0)
    
anon :: StateT Int (Reader IdS) a -> StateT Int (Reader IdS) a
anon m = get >>= \ i -> local (prefix (showString "/<anon:" . shows i . showChar '>') .) m <* modify' succ
    
symbolIdsStmt :: Parser.Stmt () -> StateT Int (Reader IdS) (Parser.Stmt Id)
symbolIdsStmt (Parser.DeclSym sym ()) = reader (\ ids ->
  (Parser.DeclSym sym . ids) (prefix (showString "/<sym:" . Parser.showSymbol sym . showChar '>') emptyId))
symbolIdsStmt (Parser.SetPun p) = pure (Parser.SetPun p)
symbolIdsStmt (l `Parser.Set` e) = (l `Parser.Set`) <$> case l of
  Parser.SetPath p -> (local (idPath p .) . reader) (symbolise e)
  _ -> get <* modify' succ
    >>= \ i -> (local (prefix (showString "/<anon:" . shows i . showChar '>') .)
      . local ((fromMaybe . prefix) (showString "/<noname>") (findIdPath l) .)
      . reader) (symbolise e)
  where
    findIdPath :: Parser.SetExpr -> Maybe IdS
    findIdPath (Parser.SetPath p) = Just (idPath p)
    findIdPath (Parser.SetBlock stmts) = asum (findIdMatchStmt <$> stmts)
    findIdPath (Parser.SetDecomp e stmts) = asum (findIdMatchStmt <$> stmts) <|> findIdPath e
    
    idPath :: Parser.Path Parser.Var -> IdS
    idPath p = prefix (Parser.showPath showVar p) where
      showVar (Parser.Priv l) = showString "/<priv:" . Parser.showText l . showChar '>'
      showVar (Parser.Pub t) = Parser.showTag t
    
    findIdMatchStmt :: Parser.MatchStmt -> Maybe IdS
    findIdMatchStmt (Parser.MatchPun p) = Just (idPath p)
    findIdMatchStmt (l `Parser.Match` se) = findIdPath se
    
    
symexpr :: String -> Parser.Syntax () -> Either ExprErrors (Ex Parser.Symbol Parser.Var)
symexpr name = expr . (flip symbolise . prefix) (showString name)
    
    

        
-- | build executable expression syntax tree
expr :: Parser.Syntax Id -> Either ExprErrors (Ex Parser.Symbol Parser.Var)
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
    updatex e w = (e `Update` (Block [] . ListO) [(Label "x", Closed (lift w))]) `At` Label "return"
    
    
collexpr = Collect . expr
      
    
stmt :: Parser.Stmt Id -> Either ExprErrors (Build (Ex Parser.Symbol Parser.Var))
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
    matchstmt (Parser.MatchPun p)   =
      buildNPath (public <$> p) (Collect . setexpr (Parser.SetPath p))
        
    matchstmt (p `Parser.Match` l)  =
      buildNPath p (Collect . setexpr l)


