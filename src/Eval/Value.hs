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
        
        
data Deps a =
  Deps { up :: Env a, down :: Env a }
  
  
type Var a = StateT (Deps a) Maybe (Endo (Maybe (Value a)))
  
  
newtype Env a =
  Env { getEnv :: Map a (Var a) }
        
        
evalExpr :: Expr a -> Env a -> StateT (Deps a) Maybe (Value a)
evalExpr (IntegerLit x) _ =
  (return . Number . fromInteger) x
  
evalExpr (NumberLit x) _ =
  (return . Number) x

evalExpr (StringLit x) _ =
  (return . String . concat) x

evalExpr (GetEnv x) e  =
  do
    r <- (lift . M.lookup x) e
    f <- r
    appEndo f Nothing

evalExpr (GetSelf x) _ =
  do
    Deps {...} <- get
    r <-
      case (M.lookup x up, M.lookup x down) of
        (Nothing, Nothing) ->
          (lift . lift) Nothing
          
        (Nothing, Just r) ->
          do
            set (Deps { up = M.insert x r up, down = M.delete x down })
            return r
            
        (Just r, _) ->
          return r
          
    f <- lift r
    appEndo f Nothing

evalExpr (r `Get` x) e =
  do
    v <- evalExpr r e
    let s = runValue v
    r <- (lift . M.lookup x . getSelf) s
    f <- (lift . runReaderT r) s
    appEndo f Nothing

evalExpr (Block (Closed stmts)) e =
  
  where
    Ctx {...} = appEndo (runReaderT (traverse (fmap Endo . Reader . evalStmt) stmts) envCtx) (Ctx { envCtx = e, selfCtx = emptyEnv })
    
    r = ReaderT (\ down -> execState selfCtx (Deps { ..., up = emptySelf }))

evalExpr (x `Extend` y) e =
  do
    v <- evalExpr x e
    w <- evalExpr y e
    (return . Node) (M.unionWith mappend (runValue w) (runValue v))

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
      
      
      
data Ctx a = 
  Ctx
    { envCtx :: Env a
    , selfCtx :: Env a
    }

    
evalStmt :: Stmt a -> Env a -> Ctx a -> Ctx a
evalStmt (Declare path) _ =
   setPath path missingMember
  where
    missingMember = (return . Endo . const) Nothing
    
evalStmt (SetPun path) e =
  evalStmt (SetPath path `Set` getPath path) e
  where
    getPath (SelfAt x) =
      GetSelf x
      
    getPath (EnvAt x) =
      GetEnv x
      
    getPath (p `At` x) =
      getPath p `Get` x

evalStmt (l `Set` r) e =
  evalSetExpr l (runReaderT (evalExpr r) e)

    
    
setPath :: Path a -> Var a -> Ctx a -> Ctx a
setPath (SelfAt x) s ctx =
  ctx { selfCtx = (Env . M.insert x s . getEnv . selfCtx) ctx }
    
setPath (EnvAt x) s ctx =
  ctx { envCtx = (Env . M.insert x s . getEnv . envCtx) ctx }
  
setPath (p `At` x) s ctx =
  setPath p (do f <- s; return (fmap . Node . alter' x f . runValue)) ctx   
  
  
alter' :: a -> (Maybe (Value a) -> Maybe (Value a)) -> Self a -> Self a
alter' x f =
  Self . M.alter (maybe rdr (liftA2 mappend rdr)) x . getSelf
  where
    rdr = (return . Endo) f
  
  
evalSetExpr :: SetExpr a -> StateT (Deps a) Maybe (Value a) -> Ctx a -> Ctx a
evalSetExpr (SetPath path) s =
  setPath path var 
  where
    var = Endo . const . Just <$> s
    
evalSetExpr (SetBlock (Closed stmts)) s =
  appEndo  evalStateT (traverse (StateT . evalMatchStmt) stmts) s
    return (appEndo (fold fs))
    
evalSetExpr (SetBlock (path :& stmts)) s =
  appEndo (fold (f:fs))
  where
    (fs, s') = runStateT (traverse (StateT . evalMatchStmt) stmts) (runValue <$> s)
    f = evalSetExpr (SetPath path) (Node <$> s')

    
evalMatchStmt :: MatchStmt a -> StateT (Deps a) Maybe (Self a) -> (Endo (Ctx a), StateT (Deps a) Maybe (Self a))
evalMatchStmt (MatchPun l) s =
  evalMatchStmt (AsPath (pathPattern l) `Match` SetPath l) s
  where 
    pathPattern :: Path a -> PathPattern a
    pathPattern (EnvAt x) =
      SelfAtP x
    
    pathPattern (SelfAt x) =
      SelfAtP x
      
    pathPattern (l `At` x) =
      pathPattern l `AtP` x
  
evalMatchStmt (p `Match` l) s' =
  (Endo (evalSetExpr l (fst <$> s'), snd <$> s')
  where
    s' = s >>= lift . evalGetPattern p
      
      
alterPattern :: PathPattern a -> (Maybe (Value a) -> Maybe (Value a)) -> Self a -> Self a
alterPatternF (SelfAtP x) f =
  alter' f x
  
alterPattern (l `AtP` x) f =
  alterPattern l (fmap (Node . alter' x f . runValue))
  
      
evalGetPattern :: PatternExpr a -> Self a -> Maybe (Value a, Self a)
evalGetPattern (AsPath p) s =
  lookupUpdatePattern p (fmap (\ w -> (w, Nothing))) s
  where
    lookupUpdatePattern :: PathPattern a -> (Maybe (Value a) -> Maybe (Value a, Maybe (Value a))) -> Self a -> Maybe (Value a, Self a)
    lookupUpdatePattern (SelfAtP x) f s =
      lookupUpdate' x f s
            
    lookupUpdatePattern (l `AtP` x) f s =
      (lookupUpdatePattern l . fmap) (fmap Node . lookupUpdate' x f . runValue) s
      
      
    lookupUpdate' :: a -> (Maybe (Value a) -> Maybe (Value a, Maybe (Value a))) -> Self a -> Maybe (Value a, Self a)
    lookupUpdate' x f s = 
      (fmap Self . M.alterF (fmap (Endo . const . Just) . f . fmap eval) . getSelf) s
      where
        eval r =
          do
            f <- runReaderT s
            appEndo f Nothing
      
evalGetPattern (AsBlock (Closed stmts)) s =
  do
    (fs, s') <- runStateT (traverse (StateT . evalAsStmt) stmts) s
    return (Node (appEndo (fold fs) emptySelf), s')
  
  
evalSetPattern :: PatternExpr a -> Value a -> Maybe (Endo (Self a))
evalSetPattern (AsPath p) v =
  (return . Endo . alterPattern p . const . Just) v
  
evalSetPattern (AsBlock (Closed stmts)) v =
  do
    fs <- evalStateT (traverse (StateT . evalAsStmt) stmts) (unNode v)
    return (fold fs)
    
            
            
evalAsStmt :: AsStmt a -> Self a -> Maybe (Endo (Self a), Self a)
evalAsStmt (AsPun patt) s =
  evalAsStmt (AsPath patt `As` AsPath patt) s
  
evalAsStmt (lp `As` rp) s = 
  do
    (w, s') <- evalGetPattern rp s
    f <- evalSetPattern lp w
    return (f, s')
    

