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
import Types.Util.List
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
flushStr :: MonadIO m => String -> m ()
flushStr str =
  liftIO (putStr str >> hFlush stdout)

  
readPrompt :: MonadIO m => String -> m String
readPrompt prompt =
  liftIO (flushStr prompt >> getLine)

  
readParser :: Parser a -> String -> Either P.ParseError a
readParser parser input =
  P.parse parser "myi" (T.pack input)
 
 
readProgram :: String -> Either P.ParseError (Expr T.Text)
readProgram =
  readParser program

  
showProgram :: String -> String
showProgram s =
  case readProgram s of
    Left e ->
      show e
      
    Right (Structure body) ->
      case body of
        [] :<: Nothing ->
          ""
          
        x : xs :<: Nothing ->
          showsuff x xs

        [] :<: Just (y :>: ys) ->
          showsuff y ys
          
        x : xs :<: Just (y :>: ys) ->
          showsuff x xs
            ++ ";\n\n"
            ++ showsuff y ys
  
  where
    showsuff x xs =
      show x ++ foldMap (\a -> ";\n\n" ++ show a) xs
    
    
loadProgram :: String -> Eval (Maybe Value)
loadProgram file =
      liftIO (readFile file)
  >>= either E.throwParseError return . readProgram
  >>= evalRvalMaybe

  
readValue :: String -> Either P.ParseError (Expr T.Text)
readValue =
  readParser (rhs <* P.eof)

  
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

        
evalRval :: Expr T.Text -> Eval Value
evalRval r =
  evalRvalMaybe r >>= maybe E.throwMissing return


evalRvalMaybe :: Expr T.Text -> Eval (Maybe Value)
evalRvalMaybe (IntegerLit x) =
  (return . Just . Number . fromInteger) x
  
evalRvalMaybe (NumberLit x) =
  (return . Just . Number) x

evalRvalMaybe (StringLit x) =
  (return . Just . String . concat) x

evalRvalMaybe (GetEnv x) =
  do
    mb <- previewEnvAt x
    maybe
      (maybe 
         (E.throwUnboundVarIn "env" x)
         id
         (keyword x))
      (return . Just)
      mb
  where
    keyword :: T.Text -> Maybe (Eval (Maybe Value))
    keyword "browse" =
      Just (browse >> return Nothing)
  
    keyword _ =
      Nothing

evalRvalMaybe (r `Get` x) =
  do
    v <- evalRval r
    self <- liftIO (viewValue v)
    maybe
      (E.throwUnboundVarIn r x)
      (fmap Just . liftIO)
      (previewCellAt x self)

evalRvalMaybe (GetSelf x) =
  do 
    mb <- previewSelfAt x
    maybe 
      (E.throwUnboundVarIn "self" x)
      (return . Just)
      mb
      
evalRvalMaybe EmptyBlock =
  return Nothing

evalRvalMaybe (Block (stmt:&stmts)) =
  do
    v <- evalScope (foldMap evalStmt (stmt:stmts))
    return (Just v)
  
evalRvalMaybe (Block (Open stmts)) =
  do
    c <- evalPack
    v <- evalScope (c <> foldMap evalStmt stmts)
    return (Just v)

evalRvalMaybe (x `Extend` y) =
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

    
evalLval :: Path T.Text -> (Maybe Cell -> IO (Maybe Cell)) -> Scope
evalLval (EnvAt x) f =
  EndoM (liftIO . M.alterF f x)
      
evalLval (SelfAt x) f =
  EndoM (\ env0 ->
    do
      tell (EndoM (liftIO . M.alterF f x) :: EndoM IOW Self)
      
      (_, self) <- ask
      
      let
        sharedCell =
          newCell
            (maybe
              (E.throwUnboundVarIn "env" x)
              id
              (previewCellAt x self))
     
      M.insert x <$> sharedCell <*> pure env0)

evalLval (l `At` x) f =
  evalLval l (fmap Just . cellAtMaybe x f)
             
    
evalStmt :: Stmt T.Text -> Scope
evalStmt (Declare l) =
  evalLval l (\ _ -> return Nothing)

evalStmt (l `Set` r) =
  EndoM (\ env0 ->
    do
      es <- ask
      appEndoM ((evalAssign l . runEval (evalRval r)) es) env0)
    
  
evalAssign :: SetExpr T.Text -> IO Value -> Scope
evalAssign (SetPath l) m =
  evalLval l (\ _ -> Just <$> newCell m)
    
evalAssign (SetBlock body) m =
  EndoM (\ env0 ->
    do
      cell <- liftIO (newCell m)
      appEndoM (evalDestructure body cell) env0)
    where
      evalDestructure ::
        BlockExpr (MatchStmt T.Text)
          -> Cell -- store value to be unpacked
          -> Scope -- scope of lval assignment
      evalDestructure body cell =
        go body mempty
          where
            go ::
              BlockExpr (MatchStmt T.Text)
                -> EndoM IO Self -- deconstructor for self fields
                -> Scope -- scope of lval assignment
            go (Open xs)) c =
              EndoM (\ env0 ->
                do
                  env1 <-
                    appEndoM (unpack cell) env0
                  
                  -- remaining self fields
                  rem <-
                    liftIO 
                      (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
                  
                  rem' <-
                    traverse (newCell . viewCell) rem
                  
                  return (M.union rem' env1))
                  
                where
                  (unpack, c') = foldMap evalLstmt xs
  
            go (x :& xs)) c =
              unpack cell
                  
                where
                  (unpack, c') = foldMap evalLstmt (x:xs)
                  
                  
                  -- value with remaining self fields
                  w =
                    newNode <*> (pure . EndoM) 
                      (\ self0 ->
                        do
                          rem <-
                            liftIO
                              (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
                         
                          return (M.union rem self0))
        
      
      evalLstmt ::
        MonadIO m => Lstmt0 -> (Cell -> Scope, EndoM m Self)
      evalLstmt (AddressS r `As` l) =
        ( \ cell ->
            evalAssign l
              (viewCell cell >>= viewValue >>= viewSelection r)
              
        , evalSelection r (\ _ -> return Nothing)
        
        )
            
      evalLstmt (Description xs `As` l) =
        ( \ cell ->
            evalAssign l (newNode <*> pure (pack cell))
        
        , c
        
        )
          where
            (pack, c) = foldMap evalMatchStmt xs
            
      evalLstmt (AsPun l) =
        evalLstmt (AddressS (toSelection l) `As` Address l)
        
        
      toSelection :: Path T.Text -> PathPattern T.Text
      toSelection (EnvAt x) =
        SelfAtP x
      
      toSelection (SelfAt x) =
        SelfAtP x
        
      toSelection (l `At` x) =
        toSelection l `AtP` x


viewSelection :: PathPattern T.Text -> Self -> IO Value
viewSelection (SelfAtP x) =
  maybe (E.throwUnboundVarIn "self" x) id . previewCellAt x

  
viewSelection (l `AtP` x) =
  maybe (E.throwUnboundVarIn l x) id . previewCellAt x
    <=< viewValue <=< viewSelection l
            
            

evalSelection :: MonadIO m => PathPattern T.Text -> (Maybe Cell -> IO (Maybe Cell)) -> EndoM m Self
evalSelection (SelectSelf x) f =
  EndoM (liftIO . M.alterF f x)
  
evalSelection (l `Select` x) f =
  evalSelection l (fmap Just . cellAtMaybe x f)
      
     
evalMatchStmt :: (MonadIO m, MonadIO n) => Match0 -> (Cell -> EndoM m Self, EndoM n Self)
evalMatchStmt (l `Match` AddressS r) =
  ( \ cell ->
      evalMatchAssign l
        (viewCell cell >>= viewValue >>= viewSelection r)
        
  , evalSelection r (\ _ -> return Nothing)
  
  )
      
evalMatchStmt (l `Match` Description xs) =
  ( \ cell ->
      evalMatchAssign l
        (newNode <*> pure (pack cell))
  
  , c
  
  )
    where
      (pack, c) = foldMap evalMatchStmt xs


evalMatchAssign ::
  MonadIO m => SelectionPattern -> IO Value -> EndoM m Self
evalMatchAssign (Plain (AddressS l)) m =
  evalSelection l (\ _ -> Just <$> newCell m)
  
evalMatchAssign (Plain (Description xs)) m =
  EndoM (\ self0 ->
    do
      cell <- newCell m
      appEndoM (unpack cell) self0)
    where 
      (unpack, _a) = foldMap evalMatchStmt xs
      _ = _a :: EndoM IO Self
          
evalMatchAssign (Packed (DescriptionP body)) m =
  EndoM (\ self0 ->
    do
      cell <- newCell m
      appEndoM (evalDescriptionP body cell) self0)
  
  
evalDescriptionP :: MonadIO m => Description1Body -> Cell -> EndoM m Self
evalDescriptionP body cell =
  go body mempty
    where
      go :: MonadIO m => Description1Body -> EndoM IO Self -> EndoM m Self
      go ([] :<: RepackRemaining :>: xs) c =
        EndoM (\ self0 ->
          do
            self <-
              liftIO
                (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
            
            self' <-
              traverse (newCell . viewCell) self
            
            appEndoM (unpack cell) (M.union self' self0))
            
          where
            (unpack, c') = foldMap evalMatchStmt xs
      
      go ([] :<: (l `MatchP` DescriptionP a) :>: xs) c =
        EndoM (\ self0 ->
          do
            cell' <- newCell w
            
            let
              v =
                newNode <*> pure
                  (evalDescriptionP a cell')
                  
            appEndoM (evalMatchAssign l v <> unpack cell) self0)
            
          where
            (unpack, c') = foldMap evalMatchStmt xs
            
            -- value with remaining self fields
            w =
              newNode <*> (pure . EndoM) 
                (\ self0 ->
                  do
                    rem <-
                      liftIO (viewCell cell >>= viewValue >>= appEndoM (c' <> c))
                   
                    return (M.union rem self0))
    
      go ((x:xs) :<: suff) c =
        unpack cell <> go (xs :<: suff) (c' <> c)
          where
            (unpack, c') = evalMatchStmt x

