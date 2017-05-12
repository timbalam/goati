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
  , console
  , readProgram
  , readValue
  , primitiveBindings
  )
import Control.Monad.Reader ( ReaderT(..), runReaderT )
import Control.Monad.Except ( ExceptT(..), runExceptT )
import Data.List.NonEmpty ( NonEmpty(..) )
  
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

runRepl :: IO ()
runRepl =
  runExceptT
    (primitiveBindings >>= \ primEnv -> runIded (runReaderT console (primEnv, emptySelf)))
  >>= either (putStrLn . show) (\ _ -> return ())

runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  runExceptT
    (do{ primEnv <- primitiveBindings
       ; runIded (runReaderT (loadProgram file) (primEnv, emptySelf))
       })
  >>= either (putStrLn . show) (\ _ -> return ())
  
    
    