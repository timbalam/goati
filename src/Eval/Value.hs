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
readProgram =
  readParser program

  
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

evalRvalMaybe (T.Rroute (T.Route r x)) =
  do
    v <- evalRval r
    w <- liftIO (viewValue v >>= viewCellAt x)
    return (Just w)

evalRvalMaybe (T.Rroute (T.Atom x)) =
  do 
    mb <- previewSelfAt x
    maybe 
      (E.throwUnboundVar x)
      (return . Just)
      mb

evalRvalMaybe (T.Rnode stmts) =
  do
    v <- evalScope (foldMap evalStmt stmts)
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
    w <- evalUnop sym v
    return (Just w)
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
    u <- evalBinop sym v w
    return (Just u)
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

    
evalLaddr :: T.Laddress -> (Maybe Cell -> IO (Maybe Cell)) -> Scope
evalLaddr (T.Lident x) f =
  EndoM (liftIO . M.alterF f x)

evalLaddr (T.Lroute (T.Route l x)) f =
  evalLaddr l (fmap Just . cellAtMaybe x f)
      
evalLaddr (T.Lroute (T.Atom x)) f =
  EndoM (\ env0 ->
    do
      tell (EndoM (liftIO . M.alterF f x) :: EndoM IOW Self)
      (_, self) <- ask
      let
        sharedCell =
          newCell (viewCellAt x self)
     
      M.insert x <$> sharedCell <*> pure env0)
             
    
evalStmt :: T.Stmt -> Scope
evalStmt (T.Declare l) =
  evalLaddr l (\ _ -> return Nothing)

evalStmt (T.Assign l r) =
  EndoM (\ env0 ->
    do
      es <- ask
      appEndoM ((evalAssign l . runEval (evalRval r)) es) env0)
        
{-
evalStmt (T.Unpack r) = 
  do
    v <- evalRval r
    return
      (EndoM (\ env0 ->
         do
           self <- liftIO (viewValue v)
           tell (EndoM (return . M.union self) :: EndoM IOW Self)
           return (M.union self env0)))
-}

evalStmt (T.Eval r) =
  EndoM (\ env0 -> 
    do
      es <- ask
      let
        eff :: () -> IO ()
        eff () = runEval (evalRvalMaybe r) es >> return ()
       
      tell (EndoM (\ self0 -> tell (EndoM eff) >> return self0 ))
      return env0)
    
  
evalAssign :: T.Lval -> IO Value -> Scope
evalAssign (T.Laddress l) m =
  evalLaddr l (\ _ -> Just <$> newCell m)
    
evalAssign (T.Lnode body) m =
  EndoM (\ env0 ->
    do
      cell <- liftIO (newCell m)
      appEndoM (evalLnodeBody body cell) env0)
    where
      evalLnodeBody ::
        T.LnodeBody
          -> Cell -- store value to be unpacked
          -> Scope -- scope of lval assignment
      evalLnodeBody body cell =
        go body mempty
          where
            go ::
              T.LnodeBody
                -> EndoM IO Self -- deconstructor for self fields
                -> Scope -- scope of lval assignment
            go (T.UnpackFirst xs) c =
              EndoM (\ env0 ->
                do
                  env1 <- appEndoM (unpack cell) env0
                  -- remaining self fields
                  rem <- liftIO (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
                  rem' <- traverse (newCell . viewCell) rem
                  return (M.union rem' env1))
                where
                  (unpack, c') = foldMap evalLstmt xs
  
            go (T.LassignPackedFirst (T.PackedPlainRnode r) l xs) c =
              EndoM (\ env0 ->
                do
                  cell' <- newCell w
                  let
                    v =
                      newNode <*> pure (evalPackedPlainRnodeBody r cell')
                    
                  appEndoM (evalAssign l v <> unpack cell) env0)
                where
                  (unpack, c') = foldMap evalLstmt xs
                  
                  
                  -- value with remaining self fields
                  w =
                    newNode <*> (pure . EndoM) 
                      (\ self0 ->
                         do
                           rem <- liftIO (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
                           return (M.union rem self0))
              
            go (T.LassignFirst x mb) c =
              unpack cell <> maybe mempty (flip go (c' <> c)) mb
                where
                  (unpack, c') = evalLstmt x
        
      
      evalLstmt :: MonadIO m => T.Lstmt -> (Cell -> Scope, EndoM m Self)
      evalLstmt (T.Lassign (T.PlainRaddress r) l) =
        ( \ cell -> evalAssign l (viewCell cell >>= viewValue >>= viewPlainRoute r)
        , evalPlainRoute r (\ _ -> return Nothing)
        )
            
      evalLstmt (T.Lassign (T.PlainRnode (T.PlainRnodeBody xs)) l) =
        ( \ cell -> evalAssign l (newNode <*> pure (pack cell))
        , c
        )
          where
            (pack, c) = foldMap evalPlainStmt xs


viewPlainRoute :: T.PlainRoute -> Self -> IO Value
viewPlainRoute (T.PlainRoute (T.Atom x)) =
  viewCellAt x
  
viewPlainRoute (T.PlainRoute (T.Route l x)) =
  viewCellAt x <=< viewValue <=< viewPlainRoute l
            
            

evalPlainRoute :: MonadIO m => T.PlainRoute -> (Maybe Cell -> IO (Maybe Cell)) -> EndoM m Self
evalPlainRoute (T.PlainRoute (T.Atom x)) f =
  EndoM (liftIO . M.alterF f x)
  
evalPlainRoute (T.PlainRoute (T.Route l x)) f =
  evalPlainRoute l (fmap Just . cellAtMaybe x f)
      
     
evalPlainStmt :: (MonadIO m, MonadIO n) => T.PlainStmt -> (Cell -> EndoM m Self, EndoM n Self)
evalPlainStmt (T.PlainAssign l (T.PlainRaddress r)) =
  ( \ cell -> evalPlainAssign l (viewCell cell >>= viewValue >>= viewPlainRoute r)
  , evalPlainRoute r (\ _ -> return Nothing)
  )
      
evalPlainStmt (T.PlainAssign l (T.PlainRnode (T.PlainRnodeBody xs))) =
  ( \ cell -> evalPlainAssign l (newNode <*> pure (pack cell))
  , c
  )
    where
      (pack, c) = foldMap evalPlainStmt xs


evalPlainAssign :: MonadIO m => T.PlainLval -> IO Value -> EndoM m Self
evalPlainAssign (T.Unpacked (T.PlainRaddress l)) m =
  evalPlainRoute l (\ _ -> Just <$> newCell m)
  
evalPlainAssign (T.Unpacked (T.PlainRnode (T.PlainRnodeBody xs))) m =
  EndoM (\ self0 ->
    do
      cell <- newCell m
      appEndoM (unpack cell) self0)
    where 
      (unpack, _a) = foldMap evalPlainStmt xs
      _ = _a :: EndoM IO Self
          
evalPlainAssign (T.Packed (T.PackedPlainRnode a)) m =
  EndoM (\ self0 ->
    do
      cell <- newCell m
      appEndoM (evalPackedPlainRnodeBody a cell) self0)
  
  
evalPackedPlainRnodeBody :: MonadIO m => T.PackedPlainRnodeBody -> Cell -> EndoM m Self
evalPackedPlainRnodeBody a cell =
  go a mempty
    where
      go :: MonadIO m => T.PackedPlainRnodeBody -> EndoM IO Self -> EndoM m Self
      go (T.RepackFirst xs) c =
        EndoM (\ self0 ->
          do
            self <- liftIO (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
            self' <- traverse (newCell . viewCell) self
            appEndoM (unpack cell) (M.union self' self0))
          where
            (unpack, c') = foldMap evalPlainStmt xs
      
      go (T.PlainAssignPackedFirst l (T.PackedPlainRnode a) xs) c =
        EndoM (\ self0 ->
          do
            cell' <- newCell w
            let
              v =
                newNode <*> pure
                  (evalPackedPlainRnodeBody a cell')
                  
            appEndoM (evalPlainAssign l v <> unpack cell) self0)
          where
            (unpack, c') = foldMap evalPlainStmt xs
            
            -- value with remaining self fields
            w =
              newNode <*> (pure . EndoM) 
                (\ self0 ->
                   do
                     rem <- liftIO (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
                     return (M.union rem self0))
    
      go (T.PlainAssignFirst x a) c =
        unpack cell <> go a (c' <> c)
          where
            (unpack, c') = evalPlainStmt x

      
    
    
    
    
    
 {-   
evalAssign (T.Lnode xs) m =
  maybe 
    ( unpack (m >>= viewValue) )
    (\ l -> evalUnpack l unpack c m)
    (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    where
      (unpack, c) = foldMap evalReversibleStmt xs
    
    
      evalReversibleStmt :: T.ReversibleStmt -> (IO Self -> Scope, EndoM IO Self)
      evalReversibleStmt (T.ReversibleAssign keyroute l) =
        ( evalAssign l . (>>= lget)
        , lset (\ _ -> return Nothing)
        )
          where
            (lget, lset) = evalPlainRoute keyroute
          
      evalReversibleStmt _ =
        mempty
      
      
      collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
      collectUnpackStmt (T.ReversibleUnpack lhs) =
        Just lhs
      
      collectUnpackStmt _ =
        Nothing
      
      
      evalUnpack :: T.Lval -> (IO Self -> Scope) -> EndoM IO Self -> IO Value -> Scope
      evalUnpack l unpack c m = 
        evalAssign l m' <> p
          where
            p =
              unpack (m >>= viewValue)
            
            m' =
              newNode
                <*> 
                  (do
                     v <- m
                     return (mapEndoM liftIO c <> unNode v))
-}
