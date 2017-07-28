{-# LANGUAGE FlexibleContexts #-}
module Lib
  ( runOne
  , runRepl
  , readProgram
  , readValue
  , readParser
  )
  where
  
import Types.Parser( FieldId(Field) )
import qualified Types.Error as E
import Types.Eval
import Version( myiReplVersion )
import Eval
  ( evalRval
  , loadProgram
  , browse
  , readProgram
  , readValue
  , readParser
  , runEval
  )
  
import Control.Monad.Reader ( ReaderT(..), runReaderT )
import Control.Monad.Except ( ExceptT(..), runExceptT )
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.Map as M


runRepl :: IO ()
runRepl =
  do
    env <-
      primitiveBindings
    
    self <-
      M.insert (Field "version")
        <$> newCell (return (String myiReplVersion))
        <*> pure emptyEnv
      
    runEval browse (env, self)

    
runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  do
    env <-
      primitiveBindings
    
    mb <-
      runEval (loadProgram file) (env, emptyEnv)
    
    maybe (return ()) (putStrLn . show) mb
  
    
    