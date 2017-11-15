{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, OverloadedStrings, RecordWildCards #-}

module Eval.Value
where

import Parser
  ( program
  , rhs
  )
import Types.Parser as P
import qualified Types.Error as E
import Types.Eval as V
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
        
        
evalExpr :: P.Expr (Vis Tag) -> Maybe (V.Expr (Vis Tag))
evalExpr (P.IntegerLit x) =
  (return . V.Number . fromInteger) x
  
evalExpr (P.NumberLit x) =
  (return . V.Number) x

evalExpr (P.StringLit x) =
  (return . V.String) x
  
evalExpr (P.Var x) =
  (return . V.Var) x
  
evalExpr (Get (expr `At` x)) =
  f <$> evalExpr expr
  where
    f e =
      V.Match
        e
        ((V.WildP . M.singleton x . V.OpenP) M.empty)
        ((Scope . Var . B) 1)
    
evalExpr (Block (BlockExpr stmts _exprs)) =
  do
    s <- cons (map evalStmt stmts)
    ClosedB <$> blockS s
  

evalExpr (x `Update` BlockExpr stmts _exprs) =
  do
    v <- evalExpr x
    m <- cons (map evalStmt stmts) >>= blockS
    
  where
    update :: M.Map Tag (Scope Tag V.Expr (Vis Tag)) -> V.Expr (Vis Tag)

evalExpr (Unop sym x) =

evalExpr (Binop sym x y) =
      
    
evalStmt :: P.Stmt Tag -> Maybe (S (Vis Tag))
evalStmt (Declare path) =

evalStmt (SetPun path) =


evalStmt (l `Set` r) =
  evalSetExpr l (evalExpr r)
  

  
evalSetExpr :: P.SetExpr (Path (Vis Tag)) (Path Tag) -> Expr (Vis Tag) -> Maybe (S (Vis Tag))
evalSetExpr (P.SetPath s) e =
  (return . pathS s) e

evalSetExpr (SetBlock stmts me) e =
  do
    m <- consM (map evalMatchStmt stmts)
    blockM m e
    
  where
    evalMatchStmt :: MatchStmt (Path (Vis Tag)) (Path Tag) -> M (Expr (Vis Tag) -> Maybe (S (Vis Tag)))
    evalMatchStmt (MatchPun l) =
    
    evalMatchStmt (p `Match` l) =
      pathM p (evalSetExpr l)
      
   
    

