{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}

module Eval.Value
where

import Parser
  ( program
  , rhs
  )
import qualified Types.Parser as T
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
 
 
readProgram :: String -> Either P.ParseError T.Rval
readProgram input =
  T.Rnode <$> readParser program input

  
showProgram :: String -> String
showProgram s =
  either show showStmts (readProgram s)
    where
      showStmts (T.Rnode (x:xs)) =
        show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
    
    
loadProgram :: String -> Eval (Maybe Value)
loadProgram file =
      liftIO (readFile file)
  >>= either E.throwParseError return . readProgram
  >>= evalRvalMaybe

  
readValue :: String -> Either P.ParseError T.Rval
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

        
evalRval :: T.Rval -> Eval Value
evalRval r =
  evalRvalMaybe r >>= maybe E.throwMissing return


evalRvalMaybe :: T.Rval -> Eval (Maybe Value)
evalRvalMaybe (T.Number x) =
  (return . Just . Number) x

evalRvalMaybe (T.String x) =
  (return . Just . String) x

evalRvalMaybe (T.Rident x) =
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
    keyword :: T.Ident -> Maybe (Eval (Maybe Value))
    keyword (T.Ident "browse") =
      Just (browse >> return Nothing)
  
    keyword _ =
      Nothing

evalRvalMaybe (T.Rroute x) =
  evalRouteMaybe x
    where
      evalRouteMaybe :: T.Route T.Rval -> Eval (Maybe Value)
      evalRouteMaybe (T.Route r x) =
        do
          v <- evalRval r
          w <- liftIO (viewValue v >>= viewCellAt x)
          return (Just w)
      
      evalRouteMaybe (T.Atom x) =
        do 
          mb <- previewSelfAt x
          maybe 
            (E.throwUnboundVar x)
            (return . Just)
            mb

evalRvalMaybe (T.Rnode stmts) =
  do
    scope <- fold <$> mapM evalStmt stmts
    v <- evalScope scope
    return (Just v)

evalRvalMaybe (T.App x y) =
  do
    v <- evalRval x
    w <- evalRval y
    u <- newNode <*> pure (unNode w <> unNode v)
    return (Just u)

evalRvalMaybe (T.Unop sym x) =
  do
    v <- evalRval x
    (fmap Just . evalUnop sym) v
  where
    evalUnop :: MonadThrow m => T.Unop -> Value -> m Value
    evalUnop sym (Number x) =
      primitiveNumberUnop sym x
    
    evalUnop sym (Bool x) =
      primitiveBoolUnop sym x
  
    evalUnop sym x =
      E.throwUnboundVar sym

evalRvalMaybe (T.Binop sym x y) =
  do
    v <- evalRval x
    w <- evalRval y
    (fmap Just . evalBinop sym v) w
  where
    evalBinop :: MonadThrow m => T.Binop -> Value -> Value -> m Value
    evalBinop sym (Number x) (Number y) =
      primitiveNumberBinop sym x y
    
    evalBinop sym (Bool x) (Bool y) =
      primitiveBoolBinop sym x y
    
    evalBinop sym x y =
      E.throwUnboundVar sym

evalRvalMaybe (T.Import x) = 
  do
    r <- evalRval x
    case r of
      String s ->
        loadProgram s
      
      _ ->
        E.throwImportError r

    
evalLaddr :: T.Laddress -> Eval ((Maybe Cell -> IO (Maybe Cell)) -> Scope)
evalLaddr (T.Lident x) =
  return (\ f -> EndoM (lift . lift . M.alterF f x))

evalLaddr (T.Lroute r) =
  evalLroute r
    where
      evalLroute :: T.Route T.Laddress -> Eval ((Maybe Cell -> IO (Maybe Cell)) -> Scope)
      evalLroute (T.Route l x) =
        (.) <$> evalLaddr l <*> pure (\ f -> fmap Just . cellAtMaybe x f)
      
      evalLroute (T.Atom x) = 
        return (\ f ->
          EndoM (\ env0 ->
            do
              tell (EndoM (lift . M.alterF f x) :: EndoM IOW Self)
              (_, self) <- ask
              let
                sharedCell =
                  newCell (viewCellAt x self)
             
              M.insert x <$> sharedCell <*> pure env0))
             
    
evalStmt :: T.Stmt -> Eval Scope
evalStmt (T.Declare l) =
  do
    lset <- evalLaddr l
    return (lset (\ _ -> return Nothing))

evalStmt (T.Assign l r) =
  do
    lassign <- evalAssign l
    return
      (EndoM (\ env0 ->
        do
          es <- ask
          appEndoM ((lassign . runEval (evalRval r)) es) env0))
        
evalStmt (T.Unpack r) = 
  do
    v <- evalRval r
    return
      (EndoM (\ env0 ->
         do
           self <- lift (lift (viewValue v))
           tell (EndoM (return . M.union self) :: EndoM IOW Self)
           return (M.union self env0)))

evalStmt (T.Eval r) =
  return
    (EndoM (\ env0 -> 
       do
         es <- ask
         let
           eff :: () -> IO ()
           eff () = runEval (evalRvalMaybe r) es >> return ()
         tell (EndoM (\ self0 -> tell (EndoM eff) >> return self0 ))
         return env0))

         
evalPlainRoute :: T.PlainRoute -> Eval (Self -> IO Value, (Maybe Cell -> IO (Maybe Cell)) -> EndoM IO Self)
evalPlainRoute (T.PlainRoute (T.Atom x)) =
  return (viewCellAt x, EndoM . flip M.alterF x)
  
evalPlainRoute (T.PlainRoute (T.Route l x)) =
  do
    (lget, lset) <- evalPlainRoute l
    return (viewCellAt x <=< viewValue <=< lget, lset . (\ f -> fmap Just . cellAtMaybe x f))
    
  
evalAssign :: T.Lval -> Eval (IO Value -> Scope)
evalAssign (T.Laddress l) =
  do
    lset <- evalLaddr l
    return (\ m -> lset (\ _ -> Just <$> newCell m))
    
evalAssign (T.Lnode xs) =
  do
    (unpack, c) <- (fmap fold . mapM evalReversibleStmt) xs
    maybe 
      (return (\ m -> unpack (m >>= viewValue) ))
      (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack c) })
      (getAlt (foldMap (Alt . collectUnpackStmt) xs))
      
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval (IO Self -> Scope, EndoM IO Self)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do
        lassign <- evalAssign l
        (lget, lset) <- evalPlainRoute keyroute
        return (\ mself -> lassign (mself >>= lget), lset (\ _ -> return Nothing))
        
    evalReversibleStmt _ =
      return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) =
      Just lhs
    
    collectUnpackStmt _ =
      Nothing
    
    
    evalUnpack :: T.Lval -> Eval ((IO Self -> Scope) -> EndoM IO Self -> IO Value -> Scope)
    evalUnpack l = 
      do
        lassign <- evalAssign l
        return (\ unpack c m ->
          let
            p =
              unpack (m >>= viewValue)
            
            m' =
              newNode <*> (m >>= \ v -> return (mapEndoM (lift . lift) c <> unNode v))
          in 
            lassign m' <> p)
        