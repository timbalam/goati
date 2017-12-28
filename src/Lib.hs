{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts #-}
module Lib
  ( showProgram
  , runProgram
  , runImports
  , browse
  , module Types
  )
where

import Parser
  ( program
  , rhs
  )
import Types.Error
import qualified Types.Parser as Parser
import Types
import Expr( expr, closed )
import Eval( getField, eval )

import qualified Data.Map as M
import System.IO
  ( hFlush
  , stdout
  , FilePath
  )
import System.FilePath( takeDirectory, (</>), normalise )
import System.Directory( getCurrentDirectory )
import Data.List.NonEmpty( NonEmpty(..), toList )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Bifunctor
import Control.Monad.State
import Text.Parsec.Text ( Parser )
import qualified Text.Parsec as P

  
-- Console / Import --
flushStr :: T.Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: T.Text -> IO (T.Text)
readPrompt prompt =
  flushStr prompt >> T.getLine

  
showProgram :: String -> String
showProgram s =
  either
    (displayError . ParseError)
    showMy
    (P.parse program "myi" (T.pack s))
    
    
throwLeftMy :: MyError a => Either a b -> IO b
throwLeftMy = either throwMy return

throwLeftList :: (MyError a, Foldable t, Functor t) => Either (t a) b -> IO b
throwLeftList = either throwList return
    
  
type ImportMap a = M.Map FilePath (Expr a)
  
  
lookupCache :: (MonadState (ImportMap a) m, MonadIO m) => FilePath -> m (Expr a)
lookupCache file = let file' = normalise file in
  gets (M.lookup file') >>= \ m -> case m of
    Just e -> return e
    Nothing -> do
      e <- loadProgram file'
      modify' (M.insert file' e)
      return e
    
    
loadProgram :: (MonadState (ImportMap a) m, MonadIO m) => FilePath -> m (Expr a)
loadProgram file =
  liftIO (T.readFile file
    >>= throwLeftMy . first ParseError . P.parse program file
    >>= throwLeftList . expr . flip Parser.Block Nothing . toList
    >>= throwLeftList . closed)
  >>= loadImports (takeDirectory file)
  
  
loadImports :: (MonadState (ImportMap a) m, MonadIO m) => FilePath -> Expr (Sym a) -> m (Expr a)
loadImports cd = fmap join . traverse (\ e -> case e of
  Intern a -> return (return a)
  Extern file -> lookupCache (cd </> file))
  
  
runImports :: Expr (Sym a) -> IO (Expr a)
runImports e = getCurrentDirectory >>= \ cd ->
  evalStateT (loadImports cd e) M.empty
      
      
runProgram :: FilePath -> IO (Expr a)
runProgram file =
  evalStateT (loadProgram file) M.empty
  >>= throwLeftMy . flip getField (Label "run")

  
evalAndPrint :: (MonadState (ImportMap Vid) m, MonadIO m) => T.Text -> m ()
evalAndPrint s =
  liftIO ((throwLeftMy . first ParseError) (P.parse (rhs <* P.eof) "myi" s)
    >>= throwLeftList . expr
    >>= throwLeftList . closed)
  >>= \ e -> liftIO getCurrentDirectory
  >>= \ cd -> loadImports cd e
  >>= liftIO . throwLeftMy . eval
  >>= (liftIO . putStrLn . showMy :: MonadIO m => Expr Vid -> m ())


browse :: IO ()
browse = evalStateT first M.empty where 
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
   
