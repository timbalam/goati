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
  , primitiveBindings
  )
import Control.Monad.Reader ( ReaderT(..), runReaderT )
import Control.Monad.Except ( ExceptT(..), runExceptT )
import Data.List.NonEmpty ( NonEmpty(..) )

import qualified Data.Map as M
  
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

runRepl :: IO ()
runRepl =
  runExceptT
    (do{ env <- primitiveBindings
       ; self <- M.insert (T.Ident "version") <$> newCell (return (Number 1)) <*> pure M.empty
       ; runIded (runReaderT browse (env, self))
       })
  >>= either (putStrLn . show) (\ _ -> return ())

runOne :: NonEmpty String -> IO ()
runOne (file:|_args) =
  runExceptT
    (do{ env <- primitiveBindings
       ; runIded (runReaderT (loadProgram file) (env, emptySelf))
       })
  >>= either (putStrLn . show) (\ _ -> return ())
  
    
    