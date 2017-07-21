{-# LANGUAGE FlexibleContexts #-}
module Lib
  ( runOne
  , runRepl
  , readProgram
  , readValue
  ) where
import Eval
  ( evalRval
  , loadProgram
  , browse
  , readProgram
  , readValue
  , runEval
  )
import Control.Monad.Reader ( ReaderT(..), runReaderT )
import Control.Monad.Except ( ExceptT(..), runExceptT )
import Data.List.NonEmpty ( NonEmpty(..) )

import qualified Data.Map as M
  
import qualified Types.Parser as T
import qualified Types.Error as E
import Types.Eval
import Version( myiReplVersion )

runRepl :: IO ()
runRepl =
  do{ env <- primitiveBindings
    ; self <- M.insert (T.Ident "version") <$> newCell (return (String myiReplVersion)) <*> pure emptyEnv
    ; runEval browse (env, self)
    }

runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  do{ env <- primitiveBindings
    ; mb <- runEval (loadProgram file) (env, emptyEnv)
    ; maybe (return ()) (putStrLn . show) mb
    }
  
    
    