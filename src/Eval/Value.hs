{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}

module Eval.Value
where

import Parser
  ( program
  , rhs
  )
import Types.Parser
import qualified Types.Error as E
import Types.Eval
import Types.Util
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
  
import Text.Parsec.String ( Parser )
import qualified Text.Parsec as P
  
  
-- Console / Import --
flushStr :: MonadIO m => String -> m ()
flushStr str =
  liftIO (putStr str >> hFlush stdout)

  
readPrompt :: MonadIO m => String -> m String
readPrompt prompt =
  liftIO (flushStr prompt >> getLine)

  
readParser :: Parser a -> String -> Either P.ParseError a
readParser parser input =
  P.parse parser "myi" input
 
 
readProgram :: String -> Either P.ParseError Rval
readProgram =
  readParser program

  
showProgram :: String -> String
showProgram s =
  either show showStmts (readProgram s)
    where
      showStmts (Structure (x:xs)) =
        show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
        
      showStmts r =
        show r
    
    
loadProgram :: String -> Eval (Maybe Value)
loadProgram file =
      liftIO (readFile file)
  >>= either E.throwParseError return . readProgram
  >>= evalRvalMaybe

  
readValue :: String -> Either P.ParseError Rval
readValue =
  readParser rhs

  
evalAndPrint :: String -> Eval ()
evalAndPrint s =
  do
    r <- either E.throwParseError return (readValue s)
    mb <- evalRvalMaybe r
    maybe (return ()) (liftIO . putStrLn . show) mb

    
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

        
evalRval :: Rval -> Eval Value
evalRval r =
  evalRvalMaybe r >>= maybe E.throwMissing return


evalRvalMaybe :: Rval -> Eval (Maybe Value)
evalRvalMaybe (NumberLit x) =
  (return . Just . Number) x

evalRvalMaybe (StringLit x) =
  (return . Just . String) x

evalRvalMaybe (GetEnv x) =
  do
    mb <- previewEnvAt x
    maybe
      (maybe 
         (E.throwUnboundVar x)
         id
         (keyword x))
      (return . Just)
      mb
  
  where
    keyword :: FieldId -> Maybe (Eval (Maybe Value))
    keyword (Field "browse") =
      Just (browse >> return Nothing)
  
    keyword _ =
      Nothing

evalRvalMaybe (r `Get` x) =
  do
    v <- evalRval r
    w <- liftIO (viewValue v >>= viewCellAt x)
    return (Just w)

evalRvalMaybe (GetSelf x) =
  do 
    mb <- previewSelfAt x
    maybe 
      (E.throwUnboundVar x)
      (return . Just)
      mb

evalRvalMaybe (Structure stmts) =
  do
    scope <- fold <$> mapM evalStmt stmts
    v <- evalScope scope
    return (Just v)

evalRvalMaybe (x `Apply` y) =
  do
    v <- evalRval x
    w <- evalRval y
    u <- newNode <*> pure (unNode w <> unNode v)
    return (Just u)

evalRvalMaybe (Unop sym x) =
  do
    v <- evalRval x
    w <- evalUnop sym v
    return (Just w)
  where
    evalUnop :: MonadThrow m => Unop -> Value -> m Value
    evalUnop sym (Number x) =
      primitiveNumberUnop sym x
    
    evalUnop sym (Bool x) =
      primitiveBoolUnop sym x
  
    evalUnop sym x =
      E.throwUnboundVar sym

evalRvalMaybe (Binop sym x y) =
  do
    v <- evalRval x
    w <- evalRval y
    u <- evalBinop sym v w
    return (Just u)
  where
    evalBinop :: MonadThrow m => Binop -> Value -> Value -> m Value
    evalBinop sym (Number x) (Number y) =
      primitiveNumberBinop sym x y
    
    evalBinop sym (Bool x) (Bool y) =
      primitiveBoolBinop sym x y
    
    evalBinop sym x y =
      E.throwUnboundVar sym

evalRvalMaybe (Import x) = 
  do
    r <- evalRval x
    case r of
      String s ->
        loadProgram s
      
      _ ->
        E.throwImportError r

    
evalLaddr :: Lval -> (Maybe Cell -> IO (Maybe Cell)) -> Scope
evalLaddr (InEnv x) f =
  EndoM (liftIO . M.alterF f x)

evalLaddr (l `In` x) f =
  evalLaddr l (fmap Just . cellAtMaybe x f)
      
evalLaddr (InSelf x) f =
  EndoM (\ env0 ->
    do
      tell (EndoM (liftIO . M.alterF f x) :: EndoM IOW Self)
      (_, self) <- ask
      let
        sharedCell =
          newCell (viewCellAt x self)
     
      M.insert x <$> sharedCell <*> pure env0)
             
    
evalStmt :: Stmt -> Eval Scope
evalStmt (Declare l) =
  return (evalLaddr l (\ _ -> return Nothing))

evalStmt (l `Set` r) =
  return
    (EndoM (\ env0 ->
      do
        es <- ask
        appEndoM ((evalAssign l . runEval (evalRval r)) es) env0))
        
evalStmt (Unpack r) = 
  do
    v <- evalRval r
    return
      (EndoM (\ env0 ->
         do
           self <- liftIO (viewValue v)
           tell (EndoM (return . M.union self) :: EndoM IOW Self)
           return (M.union self env0)))

evalStmt (Run r) =
  return
    (EndoM (\ env0 -> 
       do
         es <- ask
         let
           eff :: () -> IO ()
           eff () = runEval (evalRvalMaybe r) es >> return ()
         
         tell (EndoM (\ self0 -> tell (EndoM eff) >> return self0 ))
         return env0))

         
evalSelect :: Selection -> (Self -> IO Value, (Maybe Cell -> IO (Maybe Cell)) -> EndoM IO Self)
evalSelect (SelectSelf x) =
  (viewCellAt x, EndoM . flip M.alterF x)
  
evalSelect (l `Select` x) =
  ( viewCellAt x <=< viewValue <=< lget
  , lset . (\ f -> fmap Just . cellAtMaybe x f)
  )
    where
      (lget, lset) = evalSelect l
    
  
evalAssign :: Pattern -> IO Value -> Scope
evalAssign (Address l) m =
  evalLaddr l (\ _ -> Just <$> newCell m)
    
evalAssign (Destructure xs) m =
  maybe 
    ( unpack (m >>= viewValue) )
    (\ l -> evalUnpack l unpack c m)
    (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    where
      (unpack, c) = foldMap evalLstmt xs
    
    
      evalLstmt :: Lstmt -> (IO Self -> Scope, EndoM IO Self)
      evalLstmt (select `As` l) =
        ( evalAssign l . (>>= lget)
        , lset (\ _ -> return Nothing)
        )
          where
            (lget, lset) = evalSelect select
          
      evalLstmt _ =
        mempty
      
      
      collectUnpackStmt :: Lstmt -> Maybe Lval
      collectUnpackStmt (RemainingAs lhs) =
        Just lhs
      
      collectUnpackStmt _ =
        Nothing
      
      
      evalUnpack :: Lval -> (IO Self -> Scope) -> EndoM IO Self -> IO Value -> Scope
      evalUnpack l unpack c m = 
        evalAssign (Address l) m' <> p
          where
            p =
              unpack (m >>= viewValue)
            
            m' =
              newNode
                <*> 
                  (do
                     v <- m
                     return (mapEndoM liftIO c <> unNode v))
        