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
import qualified System.FilePath
import System.FilePath( (</>), (<.>) )
import qualified System.Directory
import Data.List.NonEmpty( NonEmpty(..), toList )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Bifunctor
import qualified Data.Maybe as Maybe
import Control.Applicative( liftA2, Alternative(..) )
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
    
  
type ImportMap = M.Map FilePath (Expr Label)

newtype ListT m a = ListT (m (Maybe (a, ListT m a)))

listTHead :: Functor m => ListT m a -> m (Maybe a)
listTHead (ListT m) = (fst <$>) <$> m
  
  
lookupCache :: (MonadState ImportMap m, MonadIO m) => FilePath -> m (Maybe (Expr Label))
lookupCache file = let file' = System.FilePath.normalise file in
  liftA2 (<|>)
    (gets (M.lookup file'))
    (do
      b <- liftIO (System.Directory.doesPathExist file')
      if b
        then do
          e <- loadProgram file'
          modify' (M.insert file' e)
          return (Just e)
        else
          return Nothing)
  
  
loadImports :: (MonadState ImportMap m, MonadIO m) => FilePath -> Expr Vid -> m (Expr Label)
loadImports cd = go where
  go = fmap join . traverse (either
    (\ (Label x) -> lookupCache (cd </> T.unpack x <.> "my")
      >>= return . Maybe.fromJust)
    (\ x -> lookupCache (cd </> T.unpack x <.> "my")
        >>= (maybe . return) (return x) return)
    . getvis)
    
  
  
  
runImports :: Expr Vid -> IO (Expr a)
runImports e = System.Directory.getCurrentDirectory >>= \ cd ->
  evalStateT (loadImports cd e) M.empty
  >>= throwLeftList . closed
  
  
loadProgram :: (MonadState ImportMap m, MonadIO m) => FilePath -> m (Expr Label)
loadProgram file =
  liftIO (T.readFile file
    >>= throwLeftMy . first ParseError . P.parse program file
    >>= throwLeftList . expr . Parser.Block . toList)
  >>= loadImports (System.FilePath.takeDirectory file)
      
      
runProgram :: [FilePath] -> FilePath -> IO (Expr a)
runProgram _dirs file =
  evalStateT (loadProgram file) M.empty
  >>= throwLeftList . closed
  >>= throwLeftMy . flip getField (Label "run")

  
evalAndPrint :: (MonadState ImportMap m, MonadIO m) => T.Text -> m ()
evalAndPrint s =
  liftIO ((throwLeftMy . first ParseError) (P.parse (rhs <* P.eof) "myi" s)
    >>= throwLeftList . expr
    >>= throwLeftList . closed)
  >>= \ e -> liftIO System.Directory.getCurrentDirectory
  >>= \ cd -> loadImports cd e
  >>= liftIO . throwLeftList . closed
  >>= liftIO . throwLeftMy . eval
  >>= (liftIO . putStrLn . showMy :: MonadIO m => Expr Vid -> m ())


browse :: IO ()
browse = evalStateT first M.empty where 
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
   
