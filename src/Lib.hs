{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, RankNTypes #-}
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
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Bifunctor
import Control.Applicative( liftA2, Alternative(..) )
import Control.Monad.State
import Control.Monad.Trans.Maybe
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
    
    
type Ex a b = Expr M.Map (Key a) b

type ImportMap a b = M.Map FilePath (Ex a b)
  
  
loadCacheProgram :: (MonadState (ImportMap a b) m, MonadIO m) => FilePath -> m (Maybe (Ex a b))
loadCacheProgram file = let file' = System.FilePath.normalise file in
  runMaybeT 
    ((MaybeT . gets) (M.lookup file')
      <|> MaybeT (do
        b <- liftIO (System.Directory.doesPathExist file')
        if b
          then do
            e <- loadProgram file'
            modify' (M.insert file' e)
            return (Just e)
          else
            return Nothing))
  
  
loadImports :: (MonadState (ImportMap a b) m, MonadIO m) => [FilePath] -> Ex a b -> m (Ex a b)
loadImports path e@(Block es se) =
  Update e . toBlock <$> getImports importSet
  where
    importSet = foldMap getImportSet es <> foldMap getImportSet se
  
    toBlock :: M.Map (Key a) (Ex a b) -> Ex a b
    toBlock = Block [] . (Closed . lift <$>)
    
    getImportSet :: E (Key a) (Ex a) b -> S.Set (Key a)
    getImportSet = foldMapBoundE (\ k -> case k of
      Label l -> S.singleton (Label l)
      _ -> mempty)
      
    getImports
      :: (MonadState (ImportMap a b) m, MonadIO m)
      => S.Set (Key a)
      -> m (M.Map (Key k) (Ex a b))
    getImports =
      sequenceA . M.fromSet (\ k ->
        (runMaybeT . asum)
          (MaybeT . loadCacheProgram . (</> (T.unpack k <.> "my")) <$> dirs))
      
loadImports _ e = return e
    
  
runImports :: Ex a b -> IO (Ex a b)
runImports e = System.Directory.getCurrentDirectory >>= \ cd ->
  evalStateT (loadImports [cd] e) M.empty
  
  
loadProgram :: (MonadState (ImportMap a b) m, MonadIO m) => FilePath -> m (Ex a b)
loadProgram file =
  liftIO (T.readFile file
    >>= throwLeftMy . P.parse program file
    >>= throwLeftList . expr . Parser.Block . toList
    >>= throwLeftList . closed)
  >>= loadImports
    [System.FilePath.dropExtension file:System.FilePath.takeDirectory file]
      
      
runProgram :: FilePath -> IO (Ex a b)
runProgram file =
  evalStateT (loadProgram file) M.empty
  >>= flip getField (Label "run")

  
evalAndPrint :: (MonadState (ImportMap a b) m, MonadIO m) => T.Text -> m ()
evalAndPrint s =
  liftIO ((throwLeftMy . first ParseError) (P.parse (rhs <* P.eof) "myi" s)
    >>= throwLeftList . expr
    >>= throwLeftList . closed)
  >>= \ e -> liftIO System.Directory.getCurrentDirectory
  >>= \ cd -> loadImports [cd] e
  >>= liftIO . eval
  >>= (liftIO . putStrLn . showMy :: MonadIO m => Ex a b -> m ())


browse :: IO ()
browse = evalStateT first M.empty where 
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
   
