{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings #-}

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


data Ctx a =
  Ctx { envCtx :: Store a, selfCtx :: Store a }
        
        
evalExpr :: Expr a -> ReaderT (Ctx a) (WriterT [a] Maybe) (Value a)
evalExpr (IntegerLit x) =
  (return . Number . fromInteger) x
  
evalExpr (NumberLit x) =
  (return . Number) x

evalExpr (StringLit x) =
  (return . String . concat) x

evalExpr (GetEnv x) =
  do
    e <- asks env
    (lift . lift . M.lookup x) e

evalExpr (GetSelf x) =
  do
    s <- asks self
    v <- (lift . lift . M.lookup x) s
    put [x]
    return v

evalExpr (r `Get` x) =
  do
    v <- evalExpr r
    (lift . lift . previewAt x) v

evalExpr (Block (Closed stmts)) =
  do
    scope (ask { self = M.empty })
  
  where
    scope ctx0 l r = 
      do
        (xs, fs) <- (runWriterT . runReaderT (traverse evalStmt stmts)) ctx
        (return . fix . appEndo) (fold fs <> initial ctx0)
    

evalExpr (x `Extend` y) =
  do
    v <- evalExpr x
    w <- evalExpr y
    extend v w

evalExpr (Unop sym x) =
  do
    v <- evalExpr x
    (lift . lift . evalUnop sym) v
  where
    evalUnop :: Unop -> Value -> Maybe Value
    evalUnop sym (Number x) =
      Just (primitiveNumberUnop sym x)
    
    evalUnop sym (Bool x) =
      Just (primitiveBoolUnop sym x)
  
    evalUnop sym x =
      Nothing

evalExpr (Binop sym x y) =
  do
    v <- evalExpr x
    w <- evalExpr y
    (lift . lift . evalBinop sym v) w
  where
    evalBinop :: Binop -> Value -> Value -> Maybe Value
    evalBinop sym (Number x) (Number y) =
      Just (primitiveNumberBinop sym x y)
    
    evalBinop sym (Bool x) (Bool y) =
      Just (primitiveBoolBinop sym x y)
    
    evalBinop sym x y =
      Nothing

    
evalStmt :: Stmt a -> ReaderT (Ctx a) (WriterT [a] Maybe) (Endo (Ctx a))
evalStmt (Declare path) =
    (return . Endo . alterPath path . const) Nothing
    
evalStmt (SetPun path) =
  evalStmt (SetPath path `Set` getPath path)
  where
    getPath (SelfAt x) =
      GetSelf x
      
    getPath (EnvAt x) =
      GetEnv x
      
    getPath (p `At` x) =
      getPath p `Get` x

evalStmt (l `Set` r) =
  do
    v <- evalExpr r
    (return . evalSetExpr l . Just) v
    
    
    
    
    
alterPath :: Path a -> (Maybe (Value a) -> Maybe (Value a)) -> Ctx a -> Ctx a
alterPath (SelfAt x) f ctx =
  ctx { selfCtx = M.alter f x (selfCtx ctx) }
  
alterPath (EnvAt x) f ctx =
  ctx { envCtx = M.alter f x (envCtx ctx) }
  
alterPath (p `At` x) f ctx =
  alterPath p (Just . Node . alterNode x f . maybe emptyNode unNode) ctx
    
    
    
alterNode :: a -> (Maybe (Value a) -> Maybe (Value a)) -> Node a -> Node a
alterNode x f node l r =
  M.alter f (node l r)
  
  
evalSetExpr :: SetExpr a -> Value a -> Maybe (Endo (Ctx a))
evalSetExpr (SetPath path) v =
  (Just . Endo . alterPath path . const . Just) v
    
evalSetExpr (SetBlock (Closed stmts)) v =
  do
    fs <- evalStateT (traverse (StateT . evalMatchStmt) stmts) (unNode v)
    return (fold fs)
    
evalSetExpr (SetBlock (path :& stmts)) v =
  do
    (node', fs) <- runStateT (traverse (StateT . evalMatchStmt) stmts) (unNode v)
    f <- evalSetExpr (SetPath path) (Node node')
    return (fold (f:fs))

    
evalMatchStmt :: MatchStmt a -> Node a -> Maybe (Endo (Ctx a), Node a)
evalMatchStmt (MatchPun l) node =
  evalMatchStmt (AsPath (pathPattern l) `Match` SetPath l) node
  where 
    pathPattern :: Path a -> PathPattern a
    pathPattern (EnvAt x) =
      SelfAtP x
    
    pathPattern (SelfAt x) =
      SelfAtP x
      
    pathPattern (l `At` x) =
      pathPattern l `AtP` x
  
evalMatchStmt (p `Match` l) node =
  do
    (w, node') <- evalGetPattern p node
    f <- evalSetExpr l w
    return (f, node')
      
      
      
alterPattern p f = runIdentity . alterPatternF p (Identity . f)
      
      
alterPatternF :: Functor f => PathPattern a -> (Maybe (Value a) -> f (Maybe (Value a))) -> Node a -> f (Node a)
alterPatternF (SelfAtP x) f = 
  alterNode x f
  
alterPatternF (l `AtP` x) f =
  alterPatternF l f'
  where
    f' :: Maybe (Value a) -> f (Maybe (Value a))
    f' = fmap (Just . Node) . alterNodeF x f . maybe newNode unNode
      
  
alterNodeF :: Functor f => a -> (Maybe (Value a) -> f (Maybe (Value a))) -> Node a -> f (Node a)
alterNodeF x f node l r =
  M.alterF f (node l r)
  
      
evalGetPattern :: PatternExpr a -> Node a -> Maybe (Value a, Node a)
evalGetPattern (AsPath p) node =
  do
    (Const w, node') <- runWriterT (alterPatternF p trap) node
    return (w, node')
  where
    trap :: Maybe (Value a) -> WriterT (Const (Value a)) Maybe b
    trap m = writer
      do
        w <- m
        return (Const w, Nothing)
      
evalGetPattern (AsBlock (Closed stmts)) node =
  do
    (fs, node') <- runStateT (traverse (state . evalAsStmt) stmts) node
    return (Node (appEndo (fold fs) emptyNode), node')
  
  
evalSetPattern :: PatternExpr a -> Value a -> Maybe (Endo (Node a))
evalSetPattern (AsPath p) v =
  (return . Endo . alterPattern p . const . Just) v
  
evalSetPattern (AsBlock (Closed stmts)) v =
  do
    fs <- evalStateT (traverse (state . evalAsStmt) stmts) (unNode v)
    return (fold fs)
    
            
            
evalAsStmt :: AsStmt a -> Node a -> Maybe (Endo (Node a), Node a)
evalAsStmt (AsPun patt) node =
  evalAsStmt (AsPath patt `As` AsPath patt) node
  
evalAsStmt (lp `As` rp) node = 
  do
    (w, node') <- evalGetPattern rp node
    f <- evalSetPattern lp w
    return (f, node')
    

