{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}

module Eval.Base
where

import Parser
  ( program
  , rhs
  )
import qualified Types.Parser as T
import qualified Types.Error as E
import Types.Eval
import Types.Util

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
   
  
-- Eval --
newtype Eval a =
  Eval (ReaderT (Env, Self) IO a)
    deriving
      ( Functor
      , Applicative
      , Monad
      , MonadIO
      , MonadReader (Env, Self)
      , MonadThrow
      )
      
      
runEval :: Eval a -> (Env, Self) -> IO a
runEval (Eval m) es = runReaderT m es

      
valueAtMaybe :: MonadIO m => T.Ident -> (Maybe Cell -> IO (Maybe Cell)) -> Maybe (m Value) -> m Value
valueAtMaybe k f mb =
  do
    c <- maybe (return emptyNode) (>>= return . unNode) mb
    newNode <*> pure (EndoM (liftIO . M.alterF f k) <> c)


valueAt :: MonadIO m => T.Ident -> (Maybe Cell -> IO (Maybe Cell)) -> Value -> m Value
valueAt k f v =
  valueAtMaybe k f (Just (return v))
  
  
cellAtMaybe :: MonadIO m => T.Ident -> (Maybe Cell -> IO (Maybe Cell)) -> Maybe Cell -> m Cell
cellAtMaybe k f Nothing =
  newCell (valueAtMaybe k f Nothing)

cellAtMaybe k f (Just ref) =
  do
    mv <- liftIO (readIORef ref)
    newCell (mv >>= valueAt k f)

  
cellAt :: MonadIO m => T.Ident -> (Maybe Cell -> IO (Maybe Cell)) -> Cell -> m Cell
cellAt k f ref =
  cellAtMaybe k f (Just ref)
  
  
configureEnv :: Scope IOW Self IO Env -> Classed IOW Self
configureEnv =
  toClassed . liftTwo . configureEnv . toConfigurable
    where
      -- Scope IXW Self IX b -> Configurable (ReaderT Self (EWriterT IXW Self IX)) b b
      -- m ~ ReaderT Self (EWriterT IXW Self IX) 
      configureEnv:: MonadFix m => Configurable m Env Env -> m Env
      configureEnv scope = configure return (scope <> initial emptyEnv)
    
      -- ReaderT Self (EWriterT (ReaderT Self IXW) Self IX) b -> Classed IXW Self
      liftTwo ::
           ReaderT a (WriterT (EndoM IOW a) IO) b
        -> ReaderT a (WriterT (EndoM (ReaderT a IOW) a) IOW) b
      liftTwo =
        mapReaderT
          (mapWriterT
            (\ m ->
               do
                 (a, w) <- lift m
                 return (a, mapEndoM lift w)))

         
configureSelf :: Classed IOW Self -> IO Self
configureSelf c =
  do
    (self, eff) <- runWriterT mself
    appEndoM eff ()
    return self
  where
    mself :: IOW Self
    mself =
      configure return (c <> initial emptyEnv)
      
      
evalScope :: Scope IOW Self IO Env -> Eval Value
evalScope scope =
  do     
    (env, _) <- ask
    newNode <*> pure (configureEnv (scope <> initial env))
    
    
previewEnvAt :: T.Ident -> Eval (Maybe Value)
previewEnvAt k =
  do
    (env, _) <- ask
    maybe
      (return Nothing)
      (fmap Just . liftIO . viewCell)
      (M.lookup k env)

      
previewSelfAt :: T.Ident -> Eval (Maybe Value)
previewSelfAt k =
  do
    (_, self) <- ask
    maybe
      (return Nothing)
      (fmap Just . liftIO . viewCell)
      (M.lookup k self)

      
viewValue :: Value -> IO Self
viewValue (Number x) =
  primitiveNumberSelf x

viewValue (String x) =
  primitiveStringSelf x

viewValue (Bool x) =
  primitiveBoolSelf x

viewValue (Node ref c) =
  liftIO (readIORef ref) >>= 
    maybe 
      (do
         self <- configureSelf c
         liftIO (writeIORef ref (Just self))
         return self)
      return
        