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


-- Scope

  
configurePartition ::
  Configurable IO (Store a) (Store a)
    -> Configurable IO (Store b) (Store b)
configureEither f endo =
  EndoM (\ sb0 ->
    (endo <> initial emptyStore)

         
configureStore :: Configurable IO (Store a) (Store a) -> IO (Store a)
configureStore c =
  configure return (c <> initial emptyStore)
      
      
evalScope :: Configurable (WriterT (EndoM IOW Self) IO) (Env, Self) Env -> Eval Value
evalScope scope =
  do     
    (env, _) <- ask
    newNode <*> pure (configureScope (scope <> EndoM (return . M.union env)))
    

evalPack :: Eval Scope
evalPack = 
  do
    (env, _) <- ask
    return
      (EndoM (\ env0 ->
        do
          tell (EndoM (return . M.union env) :: EndoM IOW Self)
          return env0))

        