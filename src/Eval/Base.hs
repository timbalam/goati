{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}

module Eval.Base
where

import Parser
  ( program
  , rhs
  )
import qualified Types.Error as E
import Types.Eval
import Types.Util.Configurable

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
   
  
-- Eval --
newtype Eval a b =
  Eval (ReaderT (Store a, Store a) IO b)
    deriving
      ( Functor
      , Applicative
      , Monad
      , MonadIO
      , MonadReader (Env, Self)
      , MonadThrow
      )
      
      
runEval :: Eval a b -> (Store a, Store a) -> IO b
runEval (Eval m) es = runReaderT m es

      

valueAtMaybe :: a -> (Maybe (Value a) -> Maybe (Value a)) -> Maybe (Value a) -> Value a
valueAtMaybe k f mb =
  Node (EndoM (M.alter f k) <> maybe emptyNode unNode mb)


valueAt :: a -> (Maybe (Value a) -> Maybe (Value a)) -> Value a -> Value a
valueAt k f v =
  valueAtMaybe k f (Just v)
  

-- Scope
data Vis a = Pub a | Priv a


type Scope = Configurable (WriterT (EndoM IOW Self) IO) (Env, Self) Env


type Classed = Configurable IOW Self Self

  
configureScope ::
  Configurable (WriterT (EndoM IOW Self) IO) (Env, Self) Env
    -> Configurable IOW Self Self
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
    
    
previewEnvAt :: (MonadReader (Env, a) m, MonadIO m) => T.Text -> m (Maybe Value)
previewEnvAt k =
  do
    (env, _) <- ask
    maybe
      (return Nothing)
      (fmap Just . liftIO . viewCell)
      (M.lookup k env)

      

previewSelfAt :: (MonadReader (a, Self) m, MonadIO m) => T.Text -> m (Maybe Value)
previewSelfAt k =
  do
    (_, self) <- ask
    maybe
      (return Nothing)
      (fmap Just . liftIO . viewCell)
      (M.lookup k self)
      

evalPack :: Eval Scope
evalPack = 
  do
    (env, _) <- ask
    return
      (EndoM (\ env0 ->
        do
          tell (EndoM (return . M.union env) :: EndoM IOW Self)
          return env0))

      
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
        