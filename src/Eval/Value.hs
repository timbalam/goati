{-# LANGUAGE FlexibleContexts #-}

module Eval.Value
where

import qualified Types.Parser as T
import Types.Eval
import Types.Util

import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer hiding
  ( Endo(Endo)
  , appEndo
  )
import qualified Data.Map as M
import Data.IORef

  
configureEnv :: Scope IXW Self IX Env -> Classed IXW Self
configureEnv =
  toClassed . liftTwo . configureEnv . toConfigurable
    where
      -- Scope IXW Self IX b -> Configurable (ReaderT Self (EWriterT IXW Self IX)) b b
      -- m ~ ReaderT Self (EWriterT IXW Self IX) 
      configureEnv:: MonadFix m => Configurable m Env Env -> m Env
      configureEnv scope = configure return (scope <> initial emptyEnv)
    
      -- ReaderT Self (EWriterT (ReaderT Self IXW) Self IX) b -> Classed IXW Self
      liftTwo ::
           ReaderT a (WriterT (EndoM IXW a) IX) b
        -> ReaderT a (WriterT (EndoM (ReaderT a IXW) a) IXW) b
      liftTwo =
        mapReaderT
          (mapWriterT
            (\ m ->
               do
                 (a, w) <- lift m
                 return (a, mapEndoM lift w)))

         
configureSelf :: Classed IXW Self -> IX Self
configureSelf c =
  do
    (self, eff) <- runWriterT mself
    appEndoM eff ()
    return self
  where
    mself :: IXW Self
    mself =
      configure return (c <> initial emptyEnv)

      
viewValue :: Value -> IX Self
viewValue (Number x) =
  primitiveNumberSelf x

viewValue (String x) =
  primitiveStringSelf x

viewValue (Bool x) =
  primitiveBoolSelf x

viewValue (Node _ ref c) =
  liftIO (readIORef ref) >>= 
    maybe 
      (do
         self <- configureSelf c
         liftIO (writeIORef ref (Just self))
         return self)
      return

      
valueAtMaybe :: T.Ident -> (Maybe Cell -> IX (Maybe Cell)) -> Maybe (IX Value) -> IX Value
valueAtMaybe k f mb =
  do
    c <- maybe (return mempty) (>>= return . unNode) mb
    newNode <*> pure (EndoM (lift . lift . M.alterF f k) <> c)


valueAt :: (MonadState Ids m, MonadIO m) => T.Ident -> (Maybe Cell -> IX (Maybe Cell)) -> Value -> m Value
valueAt k f v =
  newNode <*> pure (EndoM (lift . lift . M.alterF f k) <> unNode v)

  
cellAtMaybe :: MonadIO m => T.Ident -> (Maybe Cell -> IX (Maybe Cell)) -> Maybe Cell -> m Cell
cellAtMaybe k f Nothing =
  liftIO (newIORef (valueAtMaybe k f Nothing))

cellAtMaybe k f (Just ref) =
  cellAt k f ref

  
cellAt :: MonadIO m => T.Ident -> (Maybe Cell -> IX (Maybe Cell)) -> Cell -> m Cell
cellAt k f ref =
  liftIO
    (do
       mv <- readIORef ref
       newIORef (mv >>= valueAt k f))
        