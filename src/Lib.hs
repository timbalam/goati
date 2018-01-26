{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, RankNTypes #-}
module Lib
  ( showProgram
  , runProgram
  , runImports
  , browse
  , interpret
  , Ex_
  , module Types
  )
where

import Parser
  ( program
  , rhs
  , Parser
  , parse
  )
import Types.Parser( showProgram )
import Types.Error
import qualified Types.Parser as Parser
import Types
import Expr( closed, symexpr )
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
import Data.Foldable( asum )
import Data.Void
import Data.List( union )
import Data.Typeable
import Control.Applicative( liftA2, Alternative(..) )
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Exception( throwIO )
--import Text.Parsec.Text ( Parser )
import qualified Text.Parsec as P

  
-- Console / Import --
flushStr :: T.Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: T.Text -> IO (T.Text)
readPrompt prompt =
  flushStr prompt >> T.getLine

  
displayProgram :: String -> String
displayProgram s =
  either
    displayError
    (flip showProgram "")
    (parse program "myi" (T.pack s))
    
    
throwLeftMy :: (MyError a, Show a, Typeable a) => Either a b -> IO b
throwLeftMy = either (throwIO . MyExceptions . pure) return

throwLeftList :: (MyError a, Show a, Typeable a) => Either (NonEmpty a) b -> IO b
throwLeftList = either (throwIO . MyExceptions) return
    
    
type Ex a = Expr M.Map (Key a)


type Ex_ = Ex Void Void


data LoadState a b = LoadState
  { imports :: M.Map FilePath (Ex a b)
  , searchPath :: [FilePath]
  }
  
  
type Interpret a b = StateT (LoadState a b)
  
newState :: LoadState a b
newState = LoadState { imports = M.empty, searchPath = [] }


interpret :: Monad m => Interpret a b m c -> [FilePath] -> m c
interpret m dirs = evalStateT m (newState { searchPath = dirs })
    
  
loadProgram :: (Ord a, MonadState (LoadState a b) m, MonadIO m) => FilePath -> m (Ex a b)
loadProgram file =
  liftIO (T.readFile file
    >>= throwLeftMy . parse program file
    >>= throwLeftList . symexpr (file++"@")
      . Parser.Block . toList
    >>= throwLeftList . closed)
  >>= loadImports
    [System.FilePath.dropExtension file, System.FilePath.takeDirectory file]
      
  
loadImports :: (Ord a, MonadState (LoadState a b) m, MonadIO m) => [FilePath] -> Ex a b -> m (Ex a b)
loadImports dirs e@(Block es se) =
  Update e . toBlock <$> (gets searchPath >>= loadImportSet imports . union dirs)
  where
    imports = foldMap getImportSet es `mappend` foldMap getImportSet se
  
    toBlock :: M.Map (Key a) (Ex a b) -> Ex a b
    toBlock = Block [] . (Closed . lift <$>)
    
    getImportSet :: Ord a => Node M.Map (Key a) (E (Key a) (Ex a) b) -> M.Map (Key a) Label
    getImportSet = (foldMap . foldMapBoundE) (\ k -> case k of
      Label l -> M.singleton (Label l) l
      _ -> mempty)
      
    loadImportSet
      :: (Ord a, MonadState (LoadState a b) m, MonadIO m)
      => M.Map (Key k) Label
      -> [FilePath]
      -> m (M.Map (Key k) (Ex a b))
    loadImportSet m path =
      M.traverseMaybeWithKey (\ _ l ->
        (runMaybeT . asum)
          (MaybeT . loadCacheProgram . (</> (T.unpack l <.> "my")) <$> path))
        m
      
loadImports _ e = return e
  
  
loadCacheProgram :: (Ord a, MonadState (LoadState a b) m, MonadIO m) => FilePath -> m (Maybe (Ex a b))
loadCacheProgram file = let file' = System.FilePath.normalise file in
  runMaybeT 
    ((MaybeT . gets) (M.lookup file' . imports)
      <|> MaybeT (do
        b <- liftIO (System.Directory.doesPathExist file')
        if b
          then do
            e <- loadProgram file'
            modify' (\ s -> s{ imports = M.insert file' e (imports s) })
            return (Just e)
          else
            return Nothing))
  
  
runImports :: Ord a => FilePath -> Ex a b -> IO (Ex a b)
runImports source e = interpret (loadImports [source] e) []

      
runProgram :: [FilePath] -> FilePath -> IO Ex_
runProgram dirs file =
  flip getField (Label "run") <$> interpret (loadProgram file) dirs

  
evalAndPrint :: (MonadState (LoadState Void Void) m, MonadIO m) => T.Text -> m ()
evalAndPrint s =
  liftIO (throwLeftMy (parse (rhs <* P.eof) "myi" s)
    >>= throwLeftList . symexpr "<myi>"
    >>= throwLeftList . closed)
  >>= \ e -> liftIO System.Directory.getCurrentDirectory
  >>= \ cd -> loadImports [cd] e
  >>= (liftIO . putStrLn . showMy . eval :: (MonadIO m) => Ex_ -> m ())


browse :: (MonadState (LoadState Void Void) m, MonadIO m) => m ()
browse = first where 
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
   
