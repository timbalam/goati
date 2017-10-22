{-# LANGUAGE FlexibleContexts #-}
module Lib
  ( runOne
  , runRepl
  , readParser
  , readProgram
  , readValue
<<<<<<< HEAD
  )
  where
  
import Types.Parser ( FieldId(Field) )
=======
  , readParser
  )
  where
  
import Types.Parser( FieldId(Field) )
>>>>>>> unpack_dots
import qualified Types.Error as E
import Types.Eval
import Version( myiReplVersion )
import Eval
  ( evalRval
  , loadProgram
  , browse
  , readParser
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
<<<<<<< HEAD
    env <- primitiveBindings
    self <- M.insert (Field "version") <$> newCell (return (String myiReplVersion)) <*> pure emptyEnv
=======
    env <-
      primitiveBindings
    
    self <-
      M.insert (Field "version")
        <$> newCell (return (String myiReplVersion))
        <*> pure emptyEnv
      
>>>>>>> unpack_dots
    runEval browse (env, self)

    
runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  do
<<<<<<< HEAD
    env <- primitiveBindings
    mb <- runEval (loadProgram file) (env, emptyEnv)
=======
    env <-
      primitiveBindings
    
    mb <-
      runEval (loadProgram file) (env, emptyEnv)
    
>>>>>>> unpack_dots
    maybe (return ()) (putStrLn . show) mb
  
    
    