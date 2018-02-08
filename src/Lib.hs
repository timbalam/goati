{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}
module Lib
  ( displayProgram
  , runProgram
  , runImports
  , browse
  , interpret
  , Ex
  , resolve
  , module Types
  )
where

import Parser
  ( Parser
  , parse
  , readsMy
  , showMy
  )
import Types.Error
import qualified Types.Parser as P
import Types
import Expr( program, expr, MonadResolve(..), MonadAbstract(..) )
import Eval( getField, eval )
import Util

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
import Data.Maybe
import Data.Void
import Data.List( union, elemIndex )
import Data.Typeable
import Control.Applicative( liftA2, Alternative(..) )
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Exception( throwIO )
--import Text.Parsec.Text ( Parser )
import qualified Text.Parsec
import Bound( closed )

  
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
    showMy
    (parse (readsMy :: Parser P.Program) "myi" (T.pack s))
    
    
throwLeftMy :: (MyError a, Show a, Typeable a) => Either a b -> IO b
throwLeftMy = either (throwIO . MyExceptions . pure) return

throwLeftList :: (MyError a, Show a, Typeable a) => Either (NonEmpty a) b -> IO b
throwLeftList = either (throwIO . MyExceptions) return


-- | Concrete resolve instance
data Varctx = Varctx
  { symbols :: M.Map P.Symbol Int
  , bindings :: [Ident]
  , filename :: Maybe FilePath
  }
  
 
newVarctx :: [Ident] -> Maybe FilePath -> Varctx
newVarctx = Varctx M.empty


symlookup :: P.Symbol -> Varctx -> Maybe Int
symlookup s = M.lookup s . symbols


symlocal :: MonadState Int m => [P.Symbol] -> m (Varctx -> Varctx)
symlocal s = do 
  s' <- newset s
  return (\ ctx -> ctx { symbols = s' `M.union` symbols ctx })


idlookup :: Ident -> Varctx -> Maybe Int
idlookup l = elemIndex l . bindings
  
  
idlocal :: [Ident] -> Varctx -> Varctx
idlocal ls ctx = ctx { bindings = ls ++ bindings ctx }


resolve :: Maybe FilePath -> StateT Int (Reader Varctx) a -> a
resolve file m = runReader (evalStateT m 0) (newVarctx [] file)

  
new :: (MonadState i m, Enum i) => m i
new = state (\ i -> (succ i, i))


newset :: (MonadState i m, Enum i, Ord k) => [k] -> m (M.Map k i)
newset = sequenceA . M.fromSet (const new) . S.fromList
  

instance MonadResolve (Maybe FilePath, Int) (StateT Int (Reader Varctx)) where
  resolveSymbol s = asks (\ ctx ->
    Symbol . (,) (filename ctx) <$> symlookup s ctx)
  
  localSymbols s m = do
    f <- symlocal s
    local f m
    
    
instance MonadAbstract (StateT Int (Reader Varctx)) where
  abstractIdent = asks . idlookup
  
  localIdents = local . idlocal 
  
  envInds = asks (zipWith const [0..] . bindings)


-- | Imports
type Ex = Expr (Key (Maybe FilePath, Int))


class MonadImport m where
  resolveImport :: FilePath -> m (Maybe (Ex a))
  
  getSearchPath :: m [FilePath]
  
  setSearchPath :: [FilePath] -> m ()
  
  
loadProgram
  :: (MonadIO m, MonadImport m) => FilePath -> m (Ex a)
loadProgram file =
  liftIO (T.readFile file
    >>= throwLeftMy . parse readsMy file
    >>= throwLeftList . getCollect . resolve (Just file) . program)
  >>= loadImports
    [System.FilePath.dropExtension file, System.FilePath.takeDirectory file]
      
  
loadImports
  :: (MonadIO m, MonadImport m) => [FilePath] -> Ex a -> m (Ex a)
loadImports dirs e@(Block es se) =
  Update e . toBlock <$> (getSearchPath >>= loadImportSet imports . union dirs)
  where
    imports = foldMap (foldMap getImportSet) es `mappend` foldMap (foldMap getImportSet) se
  
    toBlock :: Ord k => M.Map k (Expr k a) -> Expr k a
    toBlock = Block [] . (Closed . lift <$>)
    
    getImportSet :: (Ord k, Foldable m) => RecK k m a -> M.Map (Key k) Ident
    getImportSet = foldMapBoundRec (\ k -> case k of
      Ident l -> M.singleton k l
      _ -> mempty)
      
    loadImportSet
      :: (MonadImport m, MonadIO m)
      => M.Map k Ident
      -> [FilePath]
      -> m (M.Map k (Ex a))
    loadImportSet m path =
      M.traverseMaybeWithKey (\ _ l ->
        (runMaybeT . asum)
          (MaybeT . resolveImport . (</> (T.unpack l <.> "my")) <$> path))
        m
      
loadImports _ e = return e

  
evalAndPrint :: (MonadImport m, MonadIO m) => T.Text -> m ()
evalAndPrint s =
  liftIO (throwLeftMy (parse (readsMy <* Text.Parsec.eof) "myi" s)
    >>= throwLeftList . getCollect . resolve Nothing . expr)
  >>= \ e -> liftIO System.Directory.getCurrentDirectory
  >>= \ cd -> loadImports [cd] e
  >>= (liftIO . putStrLn . show . eval)


browse :: (MonadImport m, MonadIO m) => m ()
browse = first where 
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first


-- | Concrete import instance
data LoaderState = LoaderState
  { imports :: M.Map FilePath (End Ex)
  , searchPath :: [FilePath]
  }
  
newLoader :: [FilePath] -> LoaderState
newLoader path = LoaderState { imports = M.empty, searchPath = path }


interpret :: StateT LoaderState IO a -> [FilePath] -> IO a
interpret s path = evalStateT s (newLoader path)


instance MonadImport (StateT LoaderState IO) where
  resolveImport file = runMaybeT (getEnd <$> (MaybeT cached <|> MaybeT disk))
    where
      file' = System.FilePath.normalise file
      
      cached = gets (M.lookup file' . imports)
      
      disk = do
        b <- liftIO (System.Directory.doesPathExist file')
        if b then Just <$> (loadProgram file' >>= cache . fromVoid) else return Nothing
          
      cache :: MonadState LoaderState m => End Ex -> m (End Ex)
      cache e = do
        modify' (\ s -> s { imports = M.insert file' e (imports s) })
        return e
  
  getSearchPath = gets searchPath
  
  setSearchPath path = modify' (\ s -> s { searchPath = path })
  
  
  
runImports :: FilePath -> Ex a -> IO (Ex a)
runImports source e = interpret (loadImports [source] e) []

      
runProgram :: [FilePath] -> FilePath -> IO (Ex a)
runProgram dirs file =
  run <$> interpret (loadProgram file) dirs
  where
    run :: forall a. Ex a -> Ex a
    run = flip getField (Ident "run")
   
