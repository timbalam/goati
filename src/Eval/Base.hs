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
  
  
-- Scope
type Scope = Configurable (WriterT (EndoM IOW Self) IO) (Env, Self) Env


type Classed = Configurable IOW Self Self

  
configureScope :: Configurable (WriterT (EndoM IOW Self) IO) (Env, Self) Env -> Configurable IOW Self Self
configureScope scope =
  EndoM (\ self0 ->
    do
      EndoM f <- mapReaderT (liftIO . execWriterT) (configureEnv scope)
      lift (f self0))
    where   
      configureEnv ::
        MonadFix m => Configurable m (Env, a) Env -> ReaderT a m Env
      configureEnv (EndoM f) =
        configure return (EndoM (curryReader . f) <> initial emptyEnv)
      
      
      curryReader ::
        ReaderT (a, b) m c -> ReaderT a (ReaderT b m) c
      curryReader m =
        ReaderT (\ env -> ReaderT (\ self -> runReaderT m (env, self)))

         
configureSelf :: Configurable IOW Self Self -> IO Self
configureSelf c =
  do
    (self, eff) <- runWriterT mself
    appEndoM eff ()
    return self
  where
    mself :: IOW Self
    mself =
      configure return (c <> initial emptyEnv)
      
      
evalScope :: Configurable (WriterT (EndoM IOW Self) IO) (Env, Self) Env -> Eval Value
evalScope scope =
  do     
    (env, _) <- ask
    newNode <*> pure (configureScope (scope <> EndoM (return . M.union env)))
    
    
previewEnvAt :: (MonadReader (Env, a) m, MonadIO m) => T.Ident -> m (Maybe Value)
previewEnvAt k =
  do
    (env, _) <- ask
    maybe
      (return Nothing)
      (fmap Just . liftIO . viewCell)
      (M.lookup k env)

      
previewSelfAt :: (MonadReader (a, Self) m, MonadIO m) => T.Ident -> m (Maybe Value)
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
  do
    mb <- readIORef ref
    maybe 
      (do
         self <- configureSelf c
         writeIORef ref (Just self)
         return self)
      return
      mb
        