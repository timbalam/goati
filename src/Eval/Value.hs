{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings, RecordWildCards #-}

module Eval.Value
where

import Parser
  ( program
  , rhs
  )
import Types.Parser
import qualified Types.Error as E
import Types.Eval
import Types.Util.Configurable
--import Types.Util.List
import Eval.Base

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer hiding ( Endo(Endo), appEndo )
import Control.Monad.Catch
import Control.Monad.Trans.Class
import Control.Applicative
import Data.Foldable ( fold )
import qualified Data.Map as M
import Data.IORef
import System.IO
  ( putStr
  , hFlush
  , stdout
  )
  
import qualified Data.Text as T
import Text.Parsec.Text ( Parser )
import qualified Text.Parsec as P
  
  
-- Console / Import --
flushStr :: String -> IO ()
flushStr str =
  putStr str >> hFlush stdout

  
readPrompt :: String -> IO String
readPrompt prompt =
  flushStr prompt >> getLine

  
readParser :: Parser a -> String -> Either P.ParseError a
readParser parser input =
  P.parse parser "myi" (T.pack input)
 
 
readProgram :: String -> Either P.ParseError (BlockExpr (Stmt T.Text) b)
readProgram =
  readParser program

  
showProgram :: String -> String
showProgram s =
  case readProgram s of
    Left e ->
      show e
      
    Right (x:|xs) ->
      x ++ foldMap (\ a -> ";\n\n" ++ showMy a) xs
    
    
loadProgram :: String -> Eval (Value T.Text)
loadProgram file =
      liftIO (readFile file)
  >>= either E.throwParseError return . readProgram
  >>= evalExpr . Block

  
readValue :: String -> Either P.ParseError (Expr T.Text)
readValue =
  readParser (rhs <* P.eof)

  
evalAndPrint :: String -> Eval ()
evalAndPrint s =
  do
    r <- either E.throwParseError return (readValue s)
    x <- evalExpr r
    (liftIO . putStrLn . show) x

    
browse :: Eval ()
browse =
  first
    where 
      first =
        readPrompt ">> " >>= rest
    
    
      rest ":q" =
        return ()
  
      rest s =
        evalAndPrint s >> first
        
        
data Vis a = Priv a | Pub a
        
        
evalExpr :: Expr Tag ->  Value (Vis Tag)
evalExpr (IntegerLit x) =
  (return . Number . fromInteger) x
  
evalExpr (NumberLit x) =
  (return . Number) x

evalExpr (StringLit x) =
  (return . String . concat) x
  
evalExpr (GetEnv x) =
  (return . Var . Priv) x
  
evalExpr (GetPath (SelfAt x)) =
  (return . Var . Pub) x
  
evalExpr (GetPath (InF expr `At` x)) =
  do
    v <- evalExpr expr
    return (v `Proj` x)
    
evalExpr (Block (Closed stmts)) =

evalExpr (x `App` y) =
  do
    v <- evalExpr x
    w <- evalExpr y
    (return . Extend v) w

evalExpr (Unop sym x) e =
  do
    v <- evalExpr x e
    (lift . lift . evalUnop sym) v
  where
    evalUnop :: Unop -> Value -> Maybe Value
    evalUnop sym (Number x) =
      primitiveNumberUnop sym x
    
    evalUnop sym (Bool x) =
      primitiveBoolUnop sym x
  
    evalUnop sym x =
      Nothing

evalExpr (Binop sym x y) e =
  do
    v <- evalExpr x e
    w <- evalExpr y e
    (lift . lift . evalBinop sym v) w
  where
    evalBinop :: Binop -> Value -> Value -> Maybe Value
    evalBinop sym (Number x) (Number y) =
      primitiveNumberBinop sym x y
    
    evalBinop sym (Bool x) (Bool y) =
      primitiveBoolBinop sym x y
    
    evalBinop sym x y =
      Nothing
      
    
evalStmt :: Stmt Tag -> M.Map (Vis Tag) (Value (Vis Tag))
evalStmt (Declare path) =
  evalSetExpr (SetPath path) ExVar

evalStmt (SetPun path) =
  evalSetExpr (SetPath path) (getPath path)
  where
    getPath :: Path a -> Value (Vis a)
    getPath (Pure x) =
      Var (Priv x)
      
    getPath (Free (SelfAt x)) =
      Var (Pub x)
    
    getPath (Free (path `At` x)) =
      getPath path `Proj` x

evalStmt (l `Set` r) =
  evalSetExpr l (evalExpr r)

  
evalSetExpr :: SetExpr Tag -> Value (Vis Tag) -> M.Map (Vis Tag) (Value (Vis Tag))
evalSetExpr (SetPath s) v =
  setPath s v
  where
    setPath :: Path Tag -> Value (Vis Tag) -> M.Map (Vis Tag) (Value (Vis Tag))
    setPath (Pure x) v =
      M.singleton (Priv x) v
      
    setPath (Free (SelfAt x)) v =
      M.singleton (Pub x) v
      
    setPath (Free (path `At` x) v =
      (setPath . path . Node . M.fromList) [(Just x, pure v), (Nothing, pure ExVar)]

evalSetExpr (SetBlock (Closed stmts)) v =
  where
    evalMatchStmt :: MatchStmt a -> Value (Vis Tag) -> M.Map (Vis Tag) (Value (Vis Tag))
    evalMatchStmt (MatchPun l) v =
      evalSetExpr (SetPath l) (getPatternExpr (SetPath (patt l) v)
      where
        patt :: Path a -> PathPattern a
        patt (Pure x) =
          InF (SelfAt x)
        
        patt (Free (path `At` x)) =
          InF (patt path `At` x)
    
    evalMatchStmt (p `Match` l) v =
      evalSetExpr l (getPatternExpr p v)
  
    
getPatternExpr :: PatternExpr Tag -> Value (Vis Tag) -> Value (Vis Tag)
getPatternExpr (SetPath p) v =
  getAlong p v
  where
    getAlong :: PathPattern a -> Value (Vis Tag) -> Value (Vis Tag)
    getAlong (InF (SelfAt x)) v =
      v `Proj` x
      
    getAlong (InF (path `At` x)) v =
      getAlong path v `Proj` x
      
getPatternExpr (SetBlock (Closed stmts)) v =

  where
    evalAsStmt :: MatchStmt (PathPattern Tag) -> Value (Vis Tag) -> M.Map Tag (Value Tag)
    evalAsStmt (MatchPun patt) v =
      
      
    evalAsStmt (l `As` r) v =
      
    
  
setPatternExpr :: PatternExpr Tag -> Value (Vis Tag) -> M.Map Tag (Value Tag)
setPatternExpr (SetPath p) v =
  (return . Endo . alterPattern p . const . Just) v
  
setPatternExpr (SetBlock (Closed stmts)) v =
  do
    fs <- evalStateT (traverse (StateT . evalAsStmt) stmts) (unNode v)
    return (fold fs)
    
            
            
evalAsStmt :: AsStmt a -> M.Map (Maybe Tag) (Value -> Maybe (Endo (Self a), Self a)
evalAsStmt (MatchPun patt) s =
  evalAsStmt (AsPath patt `As` AsPath patt) s
  
evalAsStmt (lp `Match` rp) s = 
  do
    (w, s') <- evalGetPattern rp s
    f <- evalSetPattern lp w
    return (f, s')
    

